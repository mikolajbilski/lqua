# Adapted by permission from https://github.com/IUCompilerCourse/python-student-support-code
# See EOC-LICENSE for details
import ast
from ast import (expr, stmt, Module, Name)
from x86_ast import (Jump, JumpIf, X86Program, X86Def, instr, arg, Variable, Instr, Immediate, movq, Reg, Callq, Deref, pushreg, popreg, location, ByteReg)
from cif import Begin, Goto
from cfun import FunDef, FunProgram, CFunDef, CFunProgram
from graph import UndirectedAdjList
from collections import deque
import sys
import argparse

LOG_FILE = "compiler.log"
AVAILABLE_REG = 11

ARG_REGISTERS = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]

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
    block_suffix: int
    debug: bool
    reg_count: int
    live_after: dict[tuple[str, int], set[location]]
    write_set: dict[tuple[str, int], set[location]]
    live_before_block: dict[str, set[location]]
    interference_graph: UndirectedAdjList
    vertex_colours: dict[location, int]
    used_callee: set[Reg]
    stack_var_count: int
    basic_blocks: dict[str, list[stmt]]
    function_arity: dict[str, int]
    current_function: str

    def _generate_unique_var(self) -> ast.Name:
        name = "tmp." + str(self.var_suffix)
        self.var_suffix += 1
        return ast.Name(name)

    def _generate_block_name(self) -> str:
        name = "block_" + str(self.block_suffix)
        self.block_suffix += 1
        return name

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
            case Instr(
                instr=("cmpq"),
                args=(arg() as s1, arg() as s2)
            ):
                reads.update([s1, s2])
            case Instr(
                instr=("xorq"),
                args=(arg() as s, arg() as d)
            ):
                reads.update([s, d])
                writes.update([d])
            case Instr(
                instr=("movzbq"),
                args=(arg(), arg() as d)
            ):
                reads.update([Reg("rax")])
                writes.update([d])
            case Instr(
                instr=name,
                args=(arg(),)
            ) if isinstance(name, str) and name.startswith("set"):
                writes.update([Reg("rax")])
            case Callq(
                num_args=args
            ):
                arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]
                reads.update(arg_regs[:args])
                writes.update(caller_saved)
        reads = {x for x in reads if isinstance(x, location)}
        writes = {x for x in writes if isinstance(x, location)}
        return (reads, writes)

    def sweep_block(self, label: str, block: list[instr],
                    live_before_block: dict[str, set[location]],
                    record: bool) -> set[location]:
        live: set[location] = set()
        for i in reversed(range(len(block))):
            ins = block[i]
            match ins:
                case Jump(target):
                    after = set(live_before_block.get(target, set()))
                case JumpIf(_, target):
                    after = live_before_block.get(target, set()) | live
                case _:
                    after = live
            reads, writes = self.get_reads_writes(ins)
            if record:
                self.live_after[(label, i)] = after
                self.write_set[(label, i)] = writes
            live = (after - writes) | reads
        return live

    def uncover_live(self, d: X86Def) -> None:
        blocks = d.blocks
        predecessors: dict[str, set[str]] = {label: set() for label in blocks}
        for label, block in blocks.items():
            for ins in block:
                if isinstance(ins, (Jump, JumpIf)) and ins.label in predecessors:
                    predecessors[ins.label].add(label)

        self.live_before_block = {label: set() for label in blocks}
        worklist = deque(reversed(list(blocks)))
        queued = set(blocks)
        while worklist:
            label = worklist.pop()
            queued.discard(label)
            live_before = self.sweep_block(label, blocks[label], self.live_before_block, False)
            if live_before != self.live_before_block[label]:
                self.live_before_block[label] = live_before
                for pred in predecessors[label]:
                    if pred not in queued:
                        queued.add(pred)
                        worklist.append(pred)

        self.live_after = {}
        self.write_set = {}
        for label, block in blocks.items():
            self.sweep_block(label, block, self.live_before_block, True)
        self.log("live-before sets of blocks:")
        self.log(self.live_before_block)
        self.log("live-after set:")
        self.log(self.live_after)

    def build_interference_graph(self, d: X86Def) -> None:
        self.interference_graph = UndirectedAdjList()
        for label, block in d.blocks.items():
            for i, ins in enumerate(block):
                writes = self.write_set[(label, i)]
                live_set = self.live_after[(label, i)].copy()
                if isinstance(ins, Instr) and ins.instr == "movq":
                    live_set.discard(ins.args[0])
                for d in writes:
                    self.interference_graph.add_vertex(d)
                    for v in live_set:
                        if d != v and not self.interference_graph.has_edge(d, v):
                            self.interference_graph.add_edge(d, v)
        self.log("interference graph edges:")
        self.log(self.interference_graph.edges())

    def eval_comparison(self, cmp: ast.cmpop, left: int, right: int) -> bool:
        match cmp:
            case ast.Eq():
                return left == right
            case ast.NotEq():
                return left != right
            case ast.Lt():
                return left <  right
            case ast.LtE():
                return left <= right
            case ast.Gt():
                return left >  right
            case ast.GtE():
                return left >= right
            case _:
                raise SyntaxError(f"Unsupported comparison operator: {cmp}")

    def shrink_exp(self, e: expr) -> expr:
        match e:
            case ast.Call(func=Name('input_int'), args=[]):
                return e
            case ast.Call(func=Name(f), args=args) if f in self.function_arity:
                if len(args) != self.function_arity[f]:
                    raise ValueError(f"{f}() takes {self.function_arity[f]} argument(s), {len(args)} given")
                return ast.Call(Name(f), [self.shrink_exp(a) for a in args], [])
            case Name(f) if f in self.function_arity:
                raise NotImplementedError(f"{f} is a function and cannot be used as a value")
            case ast.Constant() | Name():
                return e
            case ast.BinOp(a, op, b):
                return ast.BinOp(self.shrink_exp(a), op, self.shrink_exp(b))
            case ast.UnaryOp(op, a):
                return ast.UnaryOp(op, self.shrink_exp(a))
            case ast.Compare(left, [op], [right]):
                left_shrunk = self.shrink_exp(left)
                right_shrunk = self.shrink_exp(right)
                if isinstance(left_shrunk, ast.Constant) and isinstance(right_shrunk, ast.Constant):
                    return ast.Constant(self.eval_comparison(op, left_shrunk.value, right_shrunk.value))
                return ast.Compare(left_shrunk, [op], [right_shrunk])
            case ast.IfExp(test, body, orelse):
                return ast.IfExp(self.shrink_exp(test), self.shrink_exp(body), self.shrink_exp(orelse))
            case ast.BoolOp(ast.And(), values):
                shrunk = [self.shrink_exp(v) for v in values]
                result = shrunk[-1]
                for v in reversed(shrunk[:-1]):
                    result = ast.IfExp(v, result, ast.Constant(False))
                return result
            case ast.BoolOp(ast.Or(), values):
                shrunk = [self.shrink_exp(v) for v in values]
                result = shrunk[-1]
                for v in reversed(shrunk[:-1]):
                    result = ast.IfExp(v, ast.Constant(True), result)
                return result
            case _:
                raise SyntaxError(f"Unsupported expression type in shrink: {e}")

    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case ast.Assign(targets=[Name() as target], value=exp):
                return ast.Assign(targets=[target], value=self.shrink_exp(exp))
            case ast.Expr(value=ast.Call(func=Name('print'), args=[exp])):
                return ast.Expr(ast.Call(func=Name('print'), args=[self.shrink_exp(exp)]))
            case ast.Expr(value=ast.Call() as call):
                return ast.Expr(self.shrink_exp(call))
            case ast.If(test, body, orelse):
                return ast.If(self.shrink_exp(test),
                              [self.shrink_stmt(s) for s in body],
                              [self.shrink_stmt(s) for s in orelse]
                              )
            case ast.While(test, body, []):
                return ast.While(self.shrink_exp(test),
                                 [self.shrink_stmt(s) for s in body],
                                 []
                                 )
            case ast.Return(value):
                return ast.Return(self.shrink_exp(value))
            case _:
                raise SyntaxError(f"Unsupported statement type in shrink: {s}")

    def function_params(self, d: ast.FunctionDef) -> list[str]:
        args = d.args
        if args.defaults or args.vararg or args.kwarg or args.kwonlyargs:
            raise NotImplementedError(f"{d.name}: only plain positional parameters are supported")
        if len(args.args) > len(ARG_REGISTERS):
            raise NotImplementedError(f"{d.name} has {len(args.args)} parameters, at most {len(ARG_REGISTERS)} are supported")
        return [a.arg for a in args.args]

    def shrink(self, p: Module) -> FunProgram:
        definitions = [s for s in p.body if isinstance(s, ast.FunctionDef)]
        top_level = [s for s in p.body if not isinstance(s, ast.FunctionDef)]
        params = {d.name: self.function_params(d) for d in definitions}
        self.function_arity = {name: len(ps) for name, ps in params.items()}
        defs = [FunDef(d.name, params[d.name], [self.shrink_stmt(s) for s in d.body]) for d in definitions]
        main_body = [self.shrink_stmt(s) for s in top_level] + [ast.Return(ast.Constant(0))]
        shrunk = FunProgram(defs + [FunDef("main", [], main_body)])
        self.log("\nshrunk program:")
        self.log(shrunk)
        return shrunk

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def bind_temps(self, tmps: Temporaries, atom: expr) -> expr:
        if not tmps:
            return atom
        body = [ast.Assign(targets=[name], value=val) for (name, val) in tmps]
        return Begin(body, atom)

    def rco_exp(self, e: expr, need_atomic : bool) -> tuple[expr, Temporaries]:
        match e:
            case (ast.Constant(value=int())) as atm:
                return (atm, [])
            case Name() as atm:
                return (atm, [])
            case ast.Call(func=Name() as func, args=args):
                new_args = []
                tmps = []
                for a in args:
                    a2, tmps_a = self.rco_exp(a, True)
                    new_args.append(a2)
                    tmps += tmps_a
                e = ast.Call(func, new_args, [])
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps + [(t, e)])
                else:
                    return (e, tmps)
            case ast.BinOp(a, op, b):
                a2, tmps_a = self.rco_exp(a, True)
                b2, tmps_b = self.rco_exp(b, True)
                e = ast.BinOp(a2, op, b2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps_a + tmps_b + [(t, e)])
                else:
                    return (e, tmps_a + tmps_b)
            case ast.UnaryOp(ast.Not(), ast.Compare(left, [op], [right]) as cmp):
                cmp2, tmps = self.rco_exp(cmp, False)
                e = ast.UnaryOp(ast.Not(), cmp2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps + [(t, e)])
                else:
                    return (e, tmps)
            case ast.UnaryOp(op, a):
                a2, tmps_a = self.rco_exp(a, True)
                e = ast.UnaryOp(op, a2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps_a + [(t, e)])
                else:
                    return (e, tmps_a)
            case ast.Compare(left, [op], [right]):
                left2, tmps_l = self.rco_exp(left, True)
                right2, tmps_r = self.rco_exp(right, True)
                e = ast.Compare(left2, [op], [right2])
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, tmps_l + tmps_r + [(t, e)])
                else:
                    return (e, tmps_l + tmps_r)
            case ast.IfExp(test, body, orelse):
                test2, test_tmps = self.rco_exp(test, False)
                body2, body_tmps = self.rco_exp(body, False)
                orelse2, orelse_tmps = self.rco_exp(orelse, False)
                body2 = self.bind_temps(body_tmps, body2)
                orelse2 = self.bind_temps(orelse_tmps, orelse2)
                e = ast.IfExp(test2, body2, orelse2)
                if need_atomic:
                    t = self._generate_unique_var()
                    return (t, test_tmps + [(t, e)])
                else:
                    return (e, test_tmps)
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
            case ast.Expr(value=ast.Call() as call):
                simple_exp, temps = self.rco_exp(call, False)
                final_stmt = ast.Expr(simple_exp)
            case ast.Return(value):
                simple_exp, temps = self.rco_exp(value, False)
                final_stmt = ast.Return(simple_exp)
            case ast.If(test, body, orelse):
                test2, test_tmps = self.rco_exp(test, False)
                test_stmts = [ast.Assign(targets=[name], value=val) for (name, val) in test_tmps]
                body2 = self.rco_stmts(body)
                orelse2 = self.rco_stmts(orelse)
                return test_stmts + [ast.If(test2, body2, orelse2)]
            case ast.While(test, body, []):
                test2, test_tmps = self.rco_exp(test, False)
                return [ast.While(self.bind_temps(test_tmps, test2), self.rco_stmts(body), [])]
            case _:
                raise SyntaxError(f"Unsupported statement type when processing line: {s}")
        simple_stmts = []
        for temp in temps:
            simple_stmts.append(ast.Assign(targets=[temp[0]], value=temp[1]))
        simple_stmts.append(final_stmt)
        return simple_stmts

    def rco_stmts(self, stmts: list[stmt]) -> list[stmt]:
        result = []
        for s in stmts:
            result.extend(self.rco_stmt(s))
        return result

    def remove_complex_operands(self, p: FunProgram) -> FunProgram:
        simplified = FunProgram([FunDef(d.name, d.params, self.rco_stmts(d.body)) for d in p.defs])
        self.log("\nsimplified program:")
        self.log(simplified)
        return simplified

    def create_block(self, stmts: list[stmt],
                     basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match stmts:
            case [Goto(_)]:
                return stmts
            case _:
                name = self._generate_block_name()
                basic_blocks[name] = stmts
                return [Goto(name)]

    def explicate_effect(self, e: expr, cont: list[stmt],
                         basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match e:
            case Begin(body, result):
                cont2 = self.explicate_effect(result, cont, basic_blocks)
                return self.explicate_stmts(body, cont2, basic_blocks)
            case ast.Call():
                return [ast.Expr(e)] + cont
            case ast.IfExp(test, body, orelse):
                goto_cont = self.create_block(cont, basic_blocks)
                body2 = self.explicate_effect(body, goto_cont, basic_blocks)
                orelse2 = self.explicate_effect(orelse, goto_cont, basic_blocks)
                return self.explicate_pred(test, body2, orelse2, basic_blocks)
            case _:
                return cont

    def explicate_assign(self, rhs: expr, lhs: expr, cont: list[stmt],
                         basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match rhs:
            case Begin(body, result):
                cont2 = self.explicate_assign(result, lhs, cont, basic_blocks)
                return self.explicate_stmts(body, cont2, basic_blocks)
            case ast.IfExp(test, body, orelse):
                goto_cont = self.create_block(cont, basic_blocks)
                then_branch = self.explicate_assign(body, lhs, goto_cont, basic_blocks)
                else_branch = self.explicate_assign(orelse, lhs, goto_cont, basic_blocks)
                return self.explicate_pred(test, then_branch, else_branch, basic_blocks)
            case _:
                return [ast.Assign(targets=[lhs], value=rhs)] + cont

    def explicate_stmt(self, s: stmt, cont: list[stmt],
                       basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match s:
            case ast.Assign(targets=[lhs], value=rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case ast.Expr(value=ast.Call(func=Name('print'), args=[atm])):
                return [ast.Expr(ast.Call(func=Name('print'), args=[atm]))] + cont
            case ast.Expr(value=e):
                return self.explicate_effect(e, cont, basic_blocks)
            case ast.If(test, body, orelse):
                goto_cont = self.create_block(cont, basic_blocks)
                body2 = self.explicate_stmts(body, goto_cont, basic_blocks)
                orelse2 = self.explicate_stmts(orelse, goto_cont, basic_blocks)
                return self.explicate_pred(test, body2, orelse2, basic_blocks)
            case ast.While(test, body, []):
                goto_cont = self.create_block(cont, basic_blocks)
                header = self._generate_block_name()
                body2 = self.explicate_stmts(body, [Goto(header)], basic_blocks)
                basic_blocks[header] = self.explicate_pred(test, body2, goto_cont, basic_blocks)
                return [Goto(header)]
            case ast.Return(value):
                return self.explicate_tail(value, basic_blocks)
            case _:
                raise SyntaxError(f"Unsupported statement type in explicate_stmt: {s}")

    def explicate_tail(self, e: expr, basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match e:
            case ast.IfExp(test, body, orelse):
                return self.explicate_pred(test,
                                           self.explicate_tail(body, basic_blocks),
                                           self.explicate_tail(orelse, basic_blocks),
                                           basic_blocks)
            case Begin(body, result):
                return self.explicate_stmts(body, self.explicate_tail(result, basic_blocks), basic_blocks)
            case _:
                return [ast.Return(e)]

    def explicate_stmts(self, stmts: list[stmt], cont: list[stmt],
                        basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        for s in reversed(stmts):
            cont = self.explicate_stmt(s, cont, basic_blocks)
        return cont

    def explicate_pred(self, cond: expr, then: list[stmt], els: list[stmt],
                       basic_blocks: dict[str, list[stmt]]) -> list[stmt]:
        match cond:
            case ast.Compare(left, [cmpop], [right]):
                goto_then = self.create_block(then, basic_blocks)
                goto_els = self.create_block(els, basic_blocks)
                return [ast.If(cond, goto_then, goto_els)]
            case ast.Constant(True):
                return then
            case ast.Constant(False):
                return els
            case ast.UnaryOp(ast.Not(), operand):
                return self.explicate_pred(operand, els, then, basic_blocks)
            case ast.IfExp(test, body, orelse):
                goto_els = self.create_block(els, basic_blocks)
                goto_then = self.create_block(then, basic_blocks)
                body_branch = self.explicate_pred(body, goto_then, goto_els, basic_blocks)
                orelse_branch = self.explicate_pred(orelse, goto_then, goto_els, basic_blocks)
                return self.explicate_pred(test, body_branch, orelse_branch, basic_blocks)
            case Begin(body, result):
                result2 = self.explicate_pred(result, then, els, basic_blocks)
                return self.explicate_stmts(body, result2, basic_blocks)
            case Name() | ast.Constant():
                return [ast.If(ast.Compare(cond, [ast.Eq()], [ast.Constant(False)]),
                                self.create_block(els, basic_blocks),
                                self.create_block(then, basic_blocks))]
            case _:
                temp = self._generate_unique_var()
                return [ast.Assign(targets=[temp], value=cond)] + \
                    self.explicate_pred(temp, then, els, basic_blocks)

    def remove_unreachable_blocks(self, blocks: dict[str, list[stmt]], start: str) -> dict[str, list[stmt]]:
        reachable: set[str] = set()
        todo = [start]
        while todo:
            label = todo.pop()
            if label in reachable or label not in blocks:
                continue
            reachable.add(label)
            for s in blocks[label]:
                match s:
                    case Goto(target):
                        todo.append(target)
                    case ast.If(_, [Goto(t1)], [Goto(t2)]):
                        todo.extend([t1, t2])
        return {label: block for label, block in blocks.items() if label in reachable}

    def explicate_def(self, d: FunDef) -> CFunDef:
        basic_blocks: dict[str, list[stmt]] = {}
        cont = self.explicate_stmts(d.body, [ast.Return(ast.Constant(0))], basic_blocks)
        start = f"{d.name}_start"
        basic_blocks[start] = cont
        basic_blocks = self.remove_unreachable_blocks(basic_blocks, start)
        self.basic_blocks = basic_blocks
        return CFunDef(d.name, d.params, basic_blocks)

    def explicate_control(self, p: FunProgram) -> CFunProgram:
        prog = CFunProgram([self.explicate_def(d) for d in p.defs])
        self.log("\nexplicated blocks:")
        self.log(prog)
        return prog

    ############################################################################
    # Select Instructions
    ############################################################################

    # The expression e passed to select_arg should furthermore be an atom.
    # (But there is no type for atoms, so the type of e is given as expr.)
    def select_arg(self, e: expr) -> arg:
        match e:
            case ast.Constant(value):
                match value:
                    case bool():
                        return Immediate(1 if value else 0)
                    case int():
                        return Immediate(value)
                    case _:
                        raise SyntaxError(f"Expected atom, got: {e}")
            case Name(var):
                return Variable(var)
            case _:
                raise SyntaxError(f"Expected atom, got: {e}")

    def cmp_to_cc(self, cmp: ast.cmpop) -> str:
        match cmp:
            case ast.Eq():
                return "e"
            case ast.NotEq():
                return "ne"
            case ast.Lt():
                return "l"
            case ast.LtE():
                return "le"
            case ast.Gt():
                return "g"
            case ast.GtE():
                return "ge"
            case _:
                raise SyntaxError(f"Unsupported comparison operator: {cmp}")

    def negate_cmp(self, cmp: ast.cmpop) -> ast.cmpop:
        match cmp:
            case ast.Eq():
                return ast.NotEq()
            case ast.NotEq():
                return ast.Eq()
            case ast.Lt():
                return ast.GtE()
            case ast.GtE():
                return ast.Lt()
            case ast.Gt():
                return ast.LtE()
            case ast.LtE():
                return ast.Gt()
            case _:
                raise SyntaxError(f"Unsupported comparison operator: {cmp}")

    def select_compare(self, target: arg, cmp: ast.cmpop, left: expr, right: expr) -> list[instr]:
        left_a = self.select_arg(left)
        right_a = self.select_arg(right)
        al = ByteReg("al")
        return [
            Instr("cmpq", [right_a, left_a]),
            Instr("set" + self.cmp_to_cc(cmp), [al]),
            Instr("movzbq", [al, target]),
        ]

    def select_call(self, f: str, args: list[expr]) -> list[instr]:
        instructions = [movq(self.select_arg(a), r) for a, r in zip(args, ARG_REGISTERS)]
        instructions.append(Callq(f, len(args)))
        return instructions

    def select_stmt(self, s: stmt) -> list[instr]:
        instructions = []
        match s:
            case Goto(label):
                instructions.append(Jump(label))
            case ast.Return(value=exp):
                instructions.extend(self.select_assign(Reg("rax"), exp))
                instructions.append(Jump(f"{self.current_function}_conclusion"))
            case ast.If(
                test=ast.Compare(left, [cmpop], [right]),
                body=[Goto(l1)],
                orelse=[Goto(l2)]
            ):
                left_a = self.select_arg(left)
                right_a = self.select_arg(right)
                instructions.append(Instr("cmpq", [right_a, left_a]))
                instructions.append(JumpIf(self.cmp_to_cc(cmpop), l1))
                instructions.append(Jump(l2))
            case ast.Expr(
                value=ast.Call(
                    func=Name('print'),
                    args=[(ast.Constant(value=int()) | Name()) as atm]
                )
            ):
                printed = self.select_arg(atm)
                instructions.append(movq(printed, Reg("rdi")))
                instructions.append(Callq("print_int", 1))
            case ast.Expr(value=ast.Call(func=Name(f), args=args)):
                instructions.extend(self.select_call(f, args))
            case ast.Assign(
                targets=[Name() as target],
                value=exp
            ):
                instructions.extend(self.select_assign(self.select_arg(target), exp))
            case _:
                raise SyntaxError(f"Unsupported statement type when processing line: {str(s)}")
        return instructions

    def select_assign(self, target: arg, exp: expr) -> list[instr]:
        instructions = []
        dest = Reg("rax")
        match exp:
            case (ast.Constant(value=int()) | Name()) as a:
                a = self.select_arg(a)
                instructions.append(movq(a, target))
            case ast.Call(func=Name(f), args=args):
                instructions.extend(self.select_call(f, args))
                instructions.append(movq(dest, target))
            case ast.BinOp(
                (ast.Constant(value=int()) | Name()) as a,
                (ast.Add() | ast.Sub()) as op,
                (ast.Constant(value=int()) | Name()) as b
            ):
                a = self.select_arg(a)
                b = self.select_arg(b)
                if isinstance(op, ast.Add):
                    if b == target:
                        instructions.append(Instr("addq", [a, b]))
                    else:
                        instructions.append(movq(a, target))
                        instructions.append(Instr("addq", [b, target]))
                else:
                    if b == target:
                        instructions.append(movq(a, dest))
                        instructions.append(Instr("subq", [b, dest]))
                        instructions.append(movq(dest, target))
                    else:
                        instructions.append(movq(a, target))
                        instructions.append(Instr("subq", [b, target]))
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
            case ast.Compare(left, [cmpop], [right]):
                instructions.extend(self.select_compare(target, cmpop, left, right))
            case ast.UnaryOp(ast.Not(), ast.Compare(left, [cmpop], [right])):
                instructions.extend(self.select_compare(target, self.negate_cmp(cmpop), left, right))
            case ast.UnaryOp(
                ast.Not(),
                (ast.Constant(value=int()) | Name()) as a
            ):
                a = self.select_arg(a)
                instructions.append(movq(a, target))
                instructions.append(Instr("xorq", [Immediate(1), target]))
            case _:
                raise SyntaxError(f"Unsupported expression type when processing line: {exp}")
        return instructions

    def select_instr_body(self, block: list[stmt]) -> list[instr]:
        instructions = []
        for s in block:
            instructions.extend(self.select_stmt(s))
        return instructions

    def select_def(self, d: CFunDef) -> X86Def:
        self.current_function = d.name
        blocks = {name: self.select_instr_body(block) for name, block in d.blocks.items()}
        start = f"{d.name}_start"
        blocks[start] = [movq(r, Variable(p)) for p, r in zip(d.params, ARG_REGISTERS)] + blocks[start]
        return X86Def(d.name, blocks)

    def select_instructions(self, p: CFunProgram) -> list[X86Def]:
        defs = [self.select_def(d) for d in p.defs]
        self.log("\nafter select_instructions:")
        self.log("\n".join(str(d) for d in defs))
        return defs

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
                taken_slots = {
                    self.vertex_colours[n]
                    for n in self.interference_graph.adjacent(v)
                    if isinstance(n, Variable) and n in self.vertex_colours
                }
                i = self.reg_count
                while i in taken_slots:
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

    def allocate_registers(self, p: X86Def) -> X86Def:
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
        p.blocks = {label: [self.assign_homes_instr(ins, homes) for ins in block]
                    for label, block in p.blocks.items()}
        self.log("\nafter allocate_registers:")
        self.log(p)
        return p

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> list[instr]:
        match i:
            case Instr(instr="movq", args=(arg1, arg2)) if arg1 == arg2:
                return []
            case Instr(
                instr=("movq" | "addq" | "subq" | "cmpq") as instruction,
                args=(Deref() as arg1, Deref() as arg2)
            ):
                instructions = []
                instructions.append(movq(arg1, Reg("rax")))
                instructions.append(Instr(instruction, (Reg("rax"), arg2)))
                return instructions
            case Instr(
                instr=("movq" | "addq" | "subq" | "cmpq") as instruction,
                args=(Immediate(value as val) as arg1, arg2)
            ) if abs(val) >= 1 << 31:
                instructions = []
                instructions.append(movq(arg1, Reg("rax")))
                instructions.append(Instr(instruction, (Reg("rax"), arg2)))
                return instructions
            case Instr(instr="cmpq", args=(arg1, Immediate() as arg2)):
                return [movq(arg2, Reg("rax")), Instr("cmpq", [arg1, Reg("rax")])]
            case Instr(instr="movzbq", args=(arg1, Deref() as arg2)):
                return [Instr("movzbq", [arg1, Reg("rax")]), movq(Reg("rax"), arg2)]
            case _:
                return [i]

    def patch_instructions(self, p: X86Def) -> X86Def:
        new_body = {}
        for label, block in p.blocks.items():
            instructions = []
            for s in block:
                instructions.extend(self.patch_instr(s))
            new_body[label] = instructions
        p.blocks = new_body
        self.log("\nafter patch_instructions:")
        self.log(p)
        return p

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def round_up_to_even(self, num: int) -> int:
        return num if num % 2 == 0 else num + 1

    def prelude_and_conclusion(self, p: X86Def) -> X86Def:
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
            popreg("rbp"),
            Instr('retq', [])
        ]
        for calee in self.used_callee:
            prelude.append(Instr("pushq", [calee]))
            conclusion = [Instr("popq", [calee])] + conclusion
        if alignment > 0:
            prelude.append(Instr("subq", [Immediate(alignment), Reg("rsp")]))
            conclusion = [Instr("addq", [Immediate(alignment), Reg("rsp")])] + conclusion
        prelude.append(Jump(f"{p.name}_start"))
        p.blocks = {p.name: prelude, **p.blocks, f"{p.name}_conclusion": conclusion}
        self.log("\nfunction with prelude and conclusion:")
        self.log(p)
        return p

    def flatten(self, defs: list[X86Def]) -> X86Program:
        body: dict[str, list[instr]] = {}
        for d in defs:
            body.update(d.blocks)
        return X86Program(body=body, entries=frozenset(d.name for d in defs))

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
            shrunk = self.shrink(source_ast)
            simplified = self.remove_complex_operands(shrunk)
            c_program = self.explicate_control(simplified)
            finished = []
            for d in self.select_instructions(c_program):
                self.current_function = d.name
                self.uncover_live(d)
                self.build_interference_graph(d)
                d = self.allocate_registers(d)
                d = self.patch_instructions(d)
                finished.append(self.prelude_and_conclusion(d))
            program = self.flatten(finished)
        finally:
            if self.debug:
                self.log_file.close()
        return program

    def __init__(self, debug=False, registers=AVAILABLE_REG):
        self.var_count = 0
        self.var_suffix = 0
        self.block_suffix = 0
        self.debug = debug
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
