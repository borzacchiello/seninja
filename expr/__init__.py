import z3

from .bitvector import BV, BVV, BVS, BVExpr
from .bool_expr import Bool, BoolExpr, BoolS, BoolV
from .bitvector_array import BVArray


def ITE(cond: Bool, iftrue: BV, iffalse: BV):
    assert iftrue.size == iffalse.size
    if isinstance(cond, BoolV):
        return iftrue if cond.value else iffalse
    return BVExpr(
        iftrue.size,
        z3.If(cond.z3obj, iftrue.z3obj, iffalse.z3obj)
    )


def ITECases(cases, default: BV):
    res = default
    for cond, val in cases[::-1]:
        res = ITE(cond, val, res)
    return res


def Or(*conditions):
    res = None
    for cond in conditions:
        assert isinstance(cond, Bool)
        res = res.Or(cond) if res is not None else cond

    assert res is not None
    return res


def And(*conditions):
    res = None
    for cond in conditions:
        assert isinstance(cond, Bool)
        res = res.And(cond) if res is not None else cond

    assert res is not None
    return res


def Xor(*conditions):
    res = None
    for cond in conditions:
        assert isinstance(cond, Bool)
        res = res.Xor(cond) if res is not None else cond

    assert res is not None
    return res
