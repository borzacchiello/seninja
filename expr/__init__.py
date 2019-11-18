from expr.bitvector import BV, BVV, BVS, BVExpr
from expr.bool_expr import Bool, BoolExpr, BoolS, BoolV
import z3

def ITE(cond: Bool, iftrue: BV, iffalse: BV):
    assert iftrue.size == iffalse.size
    return BVExpr(
        iftrue.size,
        z3.If(cond.z3obj, iftrue.z3obj, iffalse.z3obj)
    )
