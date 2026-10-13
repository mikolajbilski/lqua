# Adapted by permission from https://github.com/IUCompilerCourse/python-student-support-code
# See EOC-LICENSE for details
import ast
from ast import (expr, stmt, Module, Name)
from x86_ast import (X86Program, instr, arg, Variable, Instr, Immediate)
import os
import sys

Binding = tuple[Name, expr]
Temporaries = list[Binding]


class Compiler:


    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic : bool) -> tuple[expr, Temporaries]:
        # YOUR CODE HERE
        pass        

    def rco_stmt(self, s: stmt) -> list[stmt]:
        # YOUR CODE HERE
        pass        

    def remove_complex_operands(self, p: Module) -> Module:
        # YOUR CODE HERE
        pass                

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
            case ast.Assign(
                targets=[Name(var)],
                value=exp
            ):
                match exp:
                    case (ast.Constant(value=int()) | Name()) as a:
                        arg_a = self.select_arg(a)
                        #TODO: simple assignment
                    case ast.Call(
                        func=Name('input_int'),
                        args=[]
                    ):
                        #TODO: input_int
                        pass
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.Add() | ast.Sub()) as op,
                        (ast.Constant(value=int()) | Name()) as b
                    ):
                        arg_a = self.select_arg(a)
                        arg_b = self.select_arg(b)
                        #TODO: addition/subtraction
                    case ast.UnaryOp(
                        ast.USub(),
                        (ast.Constant(value=int()) | Name()) as a
                    ):
                        arg_a = self.select_arg(a)
                        #TODO: unary minus
                    case _:
                        raise SyntaxError(f"Unspported expression type when processing line: {s}")
            case _:
                raise SyntaxError(f"Unspported statement type when processing line: {s}")
        return [Instr("s", [Immediate(2)]), Instr("s", [Immediate(2)])]     

    def select_instructions(self, p: Module) -> X86Program:
        program = X86Program(body=[])
        for s in p.body:
            program.body.extend(self.select_stmt(s))
        return program

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass        

    def assign_homes_instr(self, i: instr,
                           home: dict[Variable, arg]) -> instr:
        # YOUR CODE HERE
        pass        

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass        

def compile(source_ast: Module) -> X86Program:
    compiler = Compiler()
    program = compiler.select_instructions(source_ast)
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
