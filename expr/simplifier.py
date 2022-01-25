import sys
import z3

from ..arch.arch_x86_64 import x8664Arch
from . import BVExpr

class TritonSimplifierException(Exception):
    def __init__(self, msg):
        self.message = msg
        super().__init__(msg)

class TritonSimplifier(object):
    def __init__(self):
        try:
            import triton
        except:
            sys.stderr.write("TritonSimplifier(): you must install the Triton symbolic engine\n")
            return

        self.ctx = triton.TritonContext(
            triton.ARCH.X86_64)
        self.ast_ctx = self.ctx.getAstContext()
        self.vars = dict()

    def _expr_to_triton(self, expr:z3.BitVecRef):
        # triton z3ToTriton API seems broken...

        if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            if expr.sort().kind() == z3.Z3_ARRAY_SORT:
                raise TritonSimplifierException("arrays unsupported")
            expr_name = expr.decl().name()
            if expr_name in self.vars:
                return self.vars[expr_name]
            self.vars[expr_name] = self.ast_ctx.variable(
                self.ctx.newSymbolicVariable(expr.size(), expr.decl().name()))
            return self.vars[expr_name]

        elif expr.decl().name() in {'select', 'store'}:
            raise TritonSimplifierException("arrays unsupported")

        elif expr.decl().name() == 'bv':
            return self.ast_ctx.bv(expr.as_long(), expr.size())

        elif expr.decl().name() == 'true':
            return self.ast_ctx.bvtrue()

        elif expr.decl().name() == 'false':
            return self.ast_ctx.bvfalse()

        elif expr.decl().name() == 'concat':
            return self.ast_ctx.concat(
                list(map(self._expr_to_triton, expr.children())))

        elif expr.decl().name() == 'extract':
            h, l = expr.params()
            e = expr.children()[0]
            return self.ast_ctx.extract(h, l, self._expr_to_triton(e))

        elif expr.decl().name() == 'bvadd':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvadd(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvsub':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvsub(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvmul':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvmul(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvxor':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvxor(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvand':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvand(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvor':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvor(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvnot':
            e = expr.children()[0]
            return self.ast_ctx.bvnot(self._expr_to_triton(e))

        elif expr.decl().name() == 'bvneg':
            e = expr.children()[0]
            return self.ast_ctx.bvneg(self._expr_to_triton(e))

        elif expr.decl().name() == 'and':
            return self.ast_ctx.land(
                list(map(self._expr_to_triton, expr.children())))

        elif expr.decl().name() == 'zero_extend':
            n = expr.params()[0]
            e = expr.children()[0]
            return self.ast_ctx.zx(n, self._expr_to_triton(e))

        elif expr.decl().name() == 'sign_extend':
            n = expr.params()[0]
            e = expr.children()[0]
            return self.ast_ctx.sx(n, self._expr_to_triton(e))

        elif expr.decl().name() == 'bvashr':
            expr, shift = expr.children()
            return self.ast_ctx.bvashr(
                self._expr_to_triton(expr), self._expr_to_triton(shift))

        elif expr.decl().name() == 'bvlshr':
            expr, shift = expr.children()
            return self.ast_ctx.bvlshr(
                self._expr_to_triton(expr), self._expr_to_triton(shift))

        elif expr.decl().name() == 'bvsge':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvsge(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvsgt':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvsgt(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvsle':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvsle(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvslt':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvslt(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvule':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvule(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvult':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvult(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvuge':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvuge(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == 'bvugt':
            lhs, rhs = expr.children()
            return self.ast_ctx.bvugt(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        elif expr.decl().name() == '=':
            lhs, rhs = expr.children()
            return self.ast_ctx.equal(
                self._expr_to_triton(lhs), self._expr_to_triton(rhs))

        else:
            raise TritonSimplifierException("unsupported decl %s" % expr.decl().name())

    def simplify(self, expr):
        if not hasattr(self, "ctx"):
            return expr

        self.vars = dict()
        try:
            triton_expr = self._expr_to_triton(expr.z3obj)
        except TritonSimplifierException as e:
            sys.stderr.write(repr(e) + "\n")
            return expr

        simplified = self.ctx.synthesize(triton_expr)
        if simplified is not None and not simplified.equalTo(triton_expr):
            # Yes, yes... It is horrible, but does the job
            s = z3.Solver()
            s.add(expr.z3obj == 0)
            fake_str = "(assert (= %s (_ bv0 %d)))" % \
                (repr(simplified), expr.size)
            fake_str = "%s\n%s" % (s.to_smt2(), fake_str)
            fake_str = fake_str.replace("(check-sat)\n", "")
            z3_expr = z3.parse_smt2_string(fake_str)[-1].children()[0]
            return BVExpr(z3_expr.size(), z3_expr)
        return expr
