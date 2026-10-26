# Adapted by permission from https://github.com/IUCompilerCourse/python-student-support-code
# See EOC-LICENSE for details
import ast
from ast import (expr, stmt, Module, Name)
from x86_ast import (X86Program, instr, arg, Variable, Instr, Immediate, movq, Reg, Callq, Deref, pushreg, popreg, location)
from graph import UndirectedAdjList
import sys
import argparse

LOG_FILE = "compiler.log"
AVAILABLE_REG = 11

color_to_register = {
    0: Reg("rcx"),
    1: Reg("rdx"),
    2: Reg("rsi"),
    3: Reg("rdi"),
    4: Reg("r8"),
    5: Reg("r9"),
    6: Reg("r10"),
    7: Reg("rbx"),
    8: Reg("r12"),
    9: Reg("r13"),
    10: Reg("r14"),
    -1: Reg("rax"),
    -2: Reg("rsp"),
    -3: Reg("rbp"),
    -4: Reg("r11"),
    -5: Reg("r15"),
}

caller_saved = {
    Reg("rax"), Reg("rcx"), Reg("rdx"),
    Reg("rsi"), Reg("rdi"), Reg("r8"),
    Reg("r9"), Reg("r10"), Reg("r11")}
callee_saved = {
    Reg("rbx"), Reg("rbp"),
    Reg("r12"), Reg("r13"),
    Reg("r14"), Reg("r15"),
}

Binding = tuple[Name, expr]
Temporaries = list[Binding]


class Compiler:
    var_count: int
    var_suffix: int
    var_current_alias: dict[str, str]
    debug: bool
    reg_count: int
    live_after: dict[int, set[location]]
    write_set: dict[int, set[location]]
    interference_graph: UndirectedAdjList
    vertex_colours: dict[location, int]
    used_callee: set[Reg]
    stack_var_count: int

    def _generate_unique_var(self) -> ast.Name:
        name = "x_" + str(self.var_suffix)
        self.var_suffix += 1
        return ast.Name(name)

    def get_reads_writes(self, i: instr) -> tuple[set[location], set[location]]:
        reads = set()
        writes = set()
        match i:
            case Instr(
                instr=("movq"),
                args=(arg() as s, arg() as d)
            ):
                reads.update([s])
                writes.update([d])
            case Instr(
                instr=("addq" | "subq" | "imulq"),
                args=(arg() as s, arg() as d)
            ):
                reads.update([s, d])
                writes.update([d])
            case Instr(
                instr=("negq"),
                args=(arg() as d,)
            ):
                reads.update([d])
                writes.update([d])
            case Instr(
                instr=("imulq"),
                args=(arg(), arg() as s, arg() as d)
            ):
                reads.update([s])
                writes.update([d])
            case Instr(
                instr=("idivq"),
                args=(arg() as x,)
            ):
                reads.update([x, Reg("rax"), Reg("rdx")])
                writes.update([Reg("rax"), Reg("rdx")])
            case Instr(
                instr=("cqto"),
                args=()
            ):
                reads.update([Reg("rax")])
                writes.update([Reg("rax"), Reg("rdx")])
            case Callq(
                num_args=args
            ):
                arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]
                reads.update(arg_regs[:args])
                writes.update(caller_saved)
        reads = {x for x in reads if isinstance(x, location)}
        writes = {x for x in writes if isinstance(x, location)}
        return (reads, writes)

    def uncover_live(self, p: X86Program) -> None:
        self.live_after = {len(p.body) - 1: set()}
        self.write_set = {}
        for i in reversed(range(len(p.body))):
            reads, writes = self.get_reads_writes(p.body[i])
            self.live_after[i-1] = (self.live_after[i] - writes) | reads
            self.write_set[i] = writes.copy()
        self.log("live-after set:")
        self.log(self.live_after)

    def build_interference_graph(self, p: X86Program) -> None:
        self.interference_graph = UndirectedAdjList()
        for i in range(len(p.body)):
            writes = self.write_set[i]
            live_set = self.live_after[i].copy()
            if isinstance(p.body[i], Instr) and p.body[i].instr == "movq":
                live_set.discard(p.body[i].args[0])
            for d in writes:
                self.interference_graph.add_vertex(d)
                for v in live_set:
                    if d != v and not self.interference_graph.has_edge(d, v):
                        self.interference_graph.add_edge(d, v)
        self.log("interference graph edges:")
        self.log(self.interference_graph.edges())

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic : bool) -> tuple[expr, Temporaries]:
        match e:
            case (ast.Constant(value=int())) as atm:
                return (atm, [])
            case Name() as atm:
                if str(atm) in self.var_current_alias.keys():
                    return (self.var_current_alias[str(atm)], [])
                else:
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
                self.var_current_alias[str(target)] = self._generate_unique_var()
                final_stmt = ast.Assign(targets=[self.var_current_alias[str(target)]], value=simple_exp)
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
        self.log("\nsimplified ast:")
        self.log(ast.dump(simplified_ast))
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
                        instructions.append(movq(a, target))
                    case ast.Call(
                        func=Name('input_int'),
                        args=[]
                    ):
                        instructions.append(Callq("input_int", 0))
                        instructions.append(movq(dest, target))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.Add() | ast.Sub()) as op,
                        (ast.Constant(value=int()) | Name()) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, target))
                        ins = ""
                        match op:
                            case ast.Add():
                                ins = "addq"
                            case ast.Sub():
                                ins = "subq"
                            case ast.Mult():
                                ins = "imulq"
                        instructions.append(Instr(ins, [b, target]))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.Mult()) as op,
                        (ast.Constant(value=int())) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, dest))
                        instructions.append(Instr("imulq", [b, dest, dest]))
                        instructions.append(movq(dest, target))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.Mult()) as op,
                        (Name()) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, dest))
                        instructions.append(Instr("imulq", [b, dest]))
                        instructions.append(movq(dest, target))
                    case ast.BinOp(
                        (ast.Constant(value=int()) | Name()) as a,
                        (ast.FloorDiv() | ast.Mod()) as op,
                        (ast.Constant(value=int()) | Name()) as b
                    ):
                        a = self.select_arg(a)
                        b = self.select_arg(b)
                        instructions.append(movq(a, dest))
                        if isinstance(b, Immediate):
                            temp_var = self.select_arg(self._generate_unique_var())
                            instructions.append(movq(b, temp_var))
                            b = temp_var
                        instructions.append(Instr("cqto", []))
                        instructions.append(Instr("idivq", [b]))
                        if isinstance(op, ast.Mod):
                            dest = Reg("rdx")
                        instructions.append(movq(dest, target))
                    case ast.UnaryOp(
                        ast.USub(),
                        (ast.Constant(value=int()) | Name()) as a
                    ):
                        a = self.select_arg(a)
                        instructions.append(movq(a, target))
                        instructions.append(Instr("negq", [target]))
                    case _:
                        raise SyntaxError(f"Unsupported expression type when processing line: {str(s)}")
            case _:
                raise SyntaxError(f"Unsupported statement type when processing line: {str(s)}")
        return instructions     

    def select_instructions(self, p: Module) -> X86Program:
        program = X86Program(body=[])
        for s in p.body:
            program.body.extend(self.select_stmt(s))
        self.log("\nafter select_instructions:")
        self.log(program)
        return program

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: dict[Variable, arg]) -> arg:
        if not isinstance(a, Variable):
            return a
        if a not in home:
            self.log("assigning new home to a variable; probably will be invalid")
            self.var_count += 1
            home[a] = Deref("rbp", -8 * self.var_count)
        return home[a]

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
        self.log("\nafter assign_homes:")
        self.log(p)
        return p

    def colour_interference_graph(self) -> None:
        self.vertex_colours = {}
        self.used_callee = set()
        self.stack_var_count = 0
        for (key, val) in color_to_register.items():
            self.vertex_colours[val] = key
        vars_left = {x for x in self.interference_graph.vertices() if isinstance(x, Variable)}
        forbidden_colours: dict[Variable, set[int]] = {}
        for v in vars_left:
            forbidden_colours[v] = set()
            neighbours = self.interference_graph.adjacent(v)
            for n in neighbours:
                if n in self.vertex_colours.keys():
                    forbidden_colours[v].add(self.vertex_colours[n])
            colours_taken = len(forbidden_colours[v])
        while len(forbidden_colours.items()) > 0:
            v: Variable
            max_found = -1
            for (key, val) in forbidden_colours.items():
                if len(val) > max_found:
                    max_found = len(val)
                    v = key
            done = False
            for i in range(self.reg_count):
                if i not in forbidden_colours[v]:
                    self.vertex_colours[v] = i
                    if color_to_register[i] in callee_saved:
                        self.used_callee.add(color_to_register[i])
                    done = True
                    break
            if not done:
                i = self.reg_count
                while i in forbidden_colours[v]:
                    i += 1
                self.vertex_colours[v] = i
                stack_slot_no = i - self.reg_count + 1
                self.stack_var_count = max(stack_slot_no, self.stack_var_count)
            forbidden_colours.pop(v)
            for n in self.interference_graph.adjacent(v):
                if n in forbidden_colours.keys():
                    forbidden_colours[n].add(self.vertex_colours[v])
        self.log(vars_left)
        self.log("vertex colours:")
        self.log(self.vertex_colours)

    def allocate_registers(self, p: X86Program) -> X86Program:
        self.colour_interference_graph()
        homes = {}
        program_vars = {x for x in self.interference_graph.vertices() if isinstance(x, Variable)}
        for v in program_vars:
            home = None
            colour = self.vertex_colours[v]
            if colour < self.reg_count:
                home = color_to_register[colour]
            else:
                stack_slot = colour - self.reg_count + 1
                home = Deref("rbp", -8 * (len(self.used_callee) + stack_slot))
            homes[v] = home
        self.log("homes:")
        self.log(homes)
        new_body = []
        for ins in p.body:
            new_body.append(self.assign_homes_instr(ins, homes))
        p.body = new_body
        self.log("\nafter allocate_registers:")
        self.log(p)
        return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        match i:
            case Instr(
                instr=("movq" | "addq" | "subq") as instruction,
                args=(Deref() as arg1, Deref() as arg2)
            ):
                instructions = []
                instructions.append(movq(arg1, Reg("rax")))
                instructions.append(Instr(instruction, (Reg("rax"), arg2)))
                return instructions
            case Instr(
                instr=("movq" | "addq" | "subq") as instruction,
                args=(Immediate(value as val) as arg1, arg2)
            ) if abs(val) >= 1 << 31:
                instructions = []
                instructions.append(movq(arg1, Reg("rax")))
                instructions.append(Instr(instruction, (Reg("rax"), arg2)))
                return instructions
            case _:
                return [i]
        return [i]

    def patch_instructions(self, p: X86Program) -> X86Program:
        program = X86Program(body=[])
        for s in p.body:
            program.body.extend(self.patch_instr(s))
        self.log("\nafter patch_instructions:")
        self.log(program)
        return program    

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def round_up_to_even(self, num: int) -> int:
        return num if num % 2 == 0 else num + 1

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        callee_used_count = len(self.used_callee)
        self.log(callee_used_count)
        self.log(self.stack_var_count)
        alignment = 8 * (self.round_up_to_even(callee_used_count + self.stack_var_count) - callee_used_count)
        prelude = [
            pushreg("rbp"),
            movq(Reg("rsp"), Reg("rbp")),
        ]
        conclusion = [
            movq(Reg("rbp"), Reg("rsp")),
            movq(Immediate(0), Reg("rax")),
            popreg("rbp"),
            Instr('retq', [])
        ]
        for calee in self.used_callee:
            prelude.append(Instr("pushq", [calee]))
            conclusion = [Instr("popq", [calee])] + conclusion
        prelude.append(Instr("subq", [Immediate(alignment), Reg("rsp")]))
        conclusion = [Instr("addq", [Immediate(alignment), Reg("rsp")])] + conclusion
        final_instructions = prelude
        final_instructions.extend(p.body)
        final_instructions.extend(conclusion)
        p.body = final_instructions
        self.log("\nprogram with prelude and conclusion:")
        self.log(p)
        return p

    def old_prelude_and_conclusion(self, p: X86Program) -> X86Program:
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
        self.log("\nprogram with prelude and conclusion:")
        self.log(p)
        return p

    def log(self, msg: str) -> None:
        if not self.debug:
            return
        print(msg, file=self.log_file)

    def compile(self, source_code: str) -> X86Program:
        log_file = None
        if self.debug:
            self.log("source code:")
            self.log(source_code)
        try:
            source_ast = construct_ast(source_code)
            self.log("\nsource ast:")
            self.log(ast.dump(source_ast))
            simplified_ast = self.remove_complex_operands(source_ast)
            program = self.select_instructions(simplified_ast)
            self.uncover_live(program)
            self.build_interference_graph(program)
            program = self.allocate_registers(program)
            #program = self.assign_homes(program)
            program = self.patch_instructions(program)
            program = self.prelude_and_conclusion(program)
        finally:
            if self.debug:
                self.log_file.close()
        return program

    def __init__(self, debug=False, registers=AVAILABLE_REG):
        self.var_count = 0
        self.var_suffix = 0
        self.debug = debug
        self.var_current_alias = {}
        self.reg_count = registers
        if self.debug:
            self.log_file = open(LOG_FILE, "w")

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
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <input_file> [compiler_options]")
        exit(1)

    parser = argparse.ArgumentParser()
    parser.add_argument("input_file")
    parser.add_argument("--debug", type=bool, default=False)
    parser.add_argument("--registers", type=int, default=AVAILABLE_REG)
    args = parser.parse_args()
    input_file = args.input_file
    debug = args.debug
    registers = args.registers
    
    source_code = read_input_file(input_file)
    compiler = Compiler(debug, registers)
    compiled = compiler.compile(source_code)
    print(compiled)

if __name__ == "__main__":
    main()
