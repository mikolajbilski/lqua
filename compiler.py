# Adapted by permission from https://github.com/IUCompilerCourse/python-student-support-code
# See EOC-LICENSE for details
import ast
from ast import (expr, stmt, Module, Name)
from x86_ast import (X86Program, instr, arg, Variable, Instr, Immediate, movq, Reg, Callq, Deref, pushreg, popreg)
import os
import sys

Binding = tuple[Name, expr]
Temporaries = list[Binding]


class Compiler:
    var_count = 0


    var_suffix = 0
    def _generate_unique_var(self) -> ast.Name:
        name = "x_" + str(self.var_suffix)
        self.var_suffix += 1
        return ast.Name(name)

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic : bool) -> tuple[expr, Temporaries]:
        match e:
            case (ast.Constant(value=int()) | Name()) as atm:
                return (atm, [])
            case ast.Call(
                    func=Name('input_int'),
                    args=[]
                ):
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, [(t, e)])
                else:
                    return (e, [])
            case ast.BinOp(a, op, b):
                a2, tmps_a = self.rco_exp(a, True)
                b2, tmps_b = self.rco_exp(b, True)
                e = ast.BinOp(a2, op, b2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps_a + tmps_b + [(t, e)])
                else:
                    return (e, tmps_a + tmps_b)
            case ast.UnaryOp(op, a):
                a2, tmps_a = self.rco_exp(a, True)
                e = ast.UnaryOp(op, a2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps_a + [(t, e)])
                else:
                    return (e, tmps_a)
            case _:
                raise SyntaxError(f"Unsupported expression type when processing line: {e}")

    def rco_stmt(self, s: stmt) -> list[stmt]:
        (simple_exp, temps) = (None, None)

        match s:
            case ast.Assign(
                targets=[Name() as target],
                value=exp
            ):
                simple_exp, temps = self.rco_exp(exp, False)
                final_stmt = ast.Assign(targets=[target], value=simple_exp)
            case ast.Expr(
                value=ast.Call(
                    func=Name('print'),
                    args=[exp]
                )
            ):
                simple_exp, temps = self.rco_exp(exp, True)
                final_stmt = ast.Expr(ast.Call(func=Name('print'), args=[simple_exp]))
            case _:
                raise SyntaxError(f"Unsupported statement type when processing line: {s}")
        simple_stmts = []
        for temp in temps:
            simple_stmts.append(ast.Assign(targets=[temp[0]], value=temp[1]))
        simple_stmts.append(final_stmt)
        return simple_stmts

    def remove_complex_operands(self, p: Module) -> Module:
        simplified_ast = ast.Module(body=[], type_ignores=[])
        for s in p.body:
            simplified_ast.body.extend(self.rco_stmt(s))
        return simplified_ast     

    ############################################################################
    # Select Instructions
    ############################################################################

    # The expression e passed to select_arg should furthermore be an atom.
    # (But there is no type for atoms, so the type of e is given as expr.)
    def select_arg(self, e: expr) -> arg:
        match e:
            case ast.Constant(int(val)):
                return Immediate(val)
            case Name(var):
                return Variable(var)
            case _:
                raise SyntaxError(f"Expected atom, got: {e}")

    def select_stmt(self, s: stmt) -> list[instr]:
        instructions = []
        match s:
            case ast.Expr(
                value=ast.Call(
                    func=Name('print'),
                    args=[(ast.Constant(value=int()) | Name()) as atm]
                )
            ):
                printed = self.select_arg(atm)
                instructions.append(movq(printed, Reg("rdi")))
                instructions.append(Callq("print_int", 1))
            case ast.Assign(
                targets=[Name() as target],
                value=exp
            ):
                target = self.select_arg(target)
                dest = Reg("rax")
                match exp:
                    case (ast.Constant(value=int()) | Name()) as a:
                        a = self.select_arg(a)
                        instructions.append(movq(a, dest))
                    case ast.Call(
                        func=Name('input_int'),
                        args=[]
                    ):
                        instructions.append(Callq("input_int", 0))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.Add() | ast.Sub() | ast.Mult()) as op,
                        (ast.Constant(value=int()) | Name()) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, dest))
                        instructions.append(movq(b, Reg("rcx")))
                        ins = ""
                        match op:
                            case ast.Add():
                                ins = "addq"
                            case ast.Sub():
                                ins = "subq"
                            case ast.Mult():
                                ins = "imulq"
                        instructions.append(Instr(ins, [Reg("rcx"), dest]))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.FloorDiv() | ast.Mod()) as op,
                        (ast.Constant(value=int()) | Name()) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, dest))
                        instructions.append(movq(b, Reg("rcx")))
                        instructions.append(Instr("cqto", []))
                        instructions.append(Instr("idivq", [Reg("rcx")]))
                        if isinstance(op, ast.Mod):
                            dest = Reg("rdx")
                    case ast.UnaryOp(
                        ast.USub(),
                        (ast.Constant(value=int()) | Name()) as a
                    ):
                        a = self.select_arg(a)
                        instructions.append(movq(a, dest))
                        instructions.append(Instr("negq", [dest]))
                    case _:
                        raise SyntaxError(f"Unsupported expression type when processing line: {str(s)}")
                instructions.append(movq(dest, target))
            case _:
                raise SyntaxError(f"Unsupported statement type when processing line: {str(s)}")
        return instructions     

    def select_instructions(self, p: Module) -> X86Program:
        program = X86Program(body=[])
        for s in p.body:
            program.body.extend(self.select_stmt(s))
        return program

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        if not isinstance(a, Variable):
            return a
        if not a.id in home.keys():
            self.var_count += 1
            home[a.id] = Deref("rbp", -8 * self.var_count)
        return home[a.id]

    def assign_homes_instr(self, i: instr,
                           home: dict[Variable, arg]) -> instr:
        if not isinstance(i, Instr):
            return i
        new_args = []
        for a in i.args:
            new_args.append(self.assign_homes_arg(a, home))
        return Instr(i.instr, new_args)

    def assign_homes(self, p: X86Program) -> X86Program:
        home = {}
        # There is an implicit assumption that a Compiler object will be used for compiling a single
        # piece of code from start to finish, so we can store this value inside it. It's dirty, but it's
        # better than recounting this in prelude_and_conclusion and assign_homes_{instr, arg}
        self.var_count = 0

        new_body = []
        for ins in p.body:
            new_body.append(self.assign_homes_instr(ins, home))
        p.body = new_body
        return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instructions(self, p: X86Program) -> X86Program:
        # We made sure all instructions have at least 1 register argument in select_instructions, so we do nothing here
        return p      

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        stack_size = 8 * (self.var_count if self.var_count % 2 == 0 else self.var_count + 1)
        prelude = [
            pushreg("rbp"),
            movq(Reg("rsp"), Reg("rbp")),
            Instr("subq", [Immediate(stack_size), Reg("rsp")])
        ]
        conclusion = [
            movq(Reg("rbp"), Reg("rsp")),
            movq(Immediate(0), Reg("rax")),
            popreg("rbp"),
            Instr('retq', [])
        ]
        final_instructions = prelude
        final_instructions.extend(p.body)
        final_instructions.extend(conclusion)
        p.body = final_instructions
        return p

def compile(source_ast: Module) -> X86Program:
    compiler = Compiler()
    simplified_ast = compiler.remove_complex_operands(source_ast)
    program = compiler.select_instructions(simplified_ast)
    program = compiler.assign_homes(program)
    program = compiler.patch_instructions(program)
    program = compiler.prelude_and_conclusion(program)
    return program

def construct_ast(source_code: str) -> Module:
    return ast.parse(source_code)

def read_input_file(path: str) -> str:
    try:
        with open(sys.argv[1], "r") as source_file:
            return source_file.read()
    except OSError as e:
        print(f"Error while reading the source file: {e}")
        exit(1)

def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <input_file>")
        exit(1)
    
    source_code = read_input_file(sys.argv[1])
    ast = construct_ast(source_code)
    compiled = compile(ast)
    print(compiled)

if __name__ == "__main__":
    main()
