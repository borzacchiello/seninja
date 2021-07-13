from ..expr import BV, BVV
import z3

MIN_BASE = 0x10000


def split_bv_in_list(bv: BV, size: int) -> list:
    assert size % 8 == 0
    res = []
    for i in range(0, bv.size, size):
        b = bv.Extract(i+size-1, i)
        res.append(b)
    return res


def bvv_from_bytes(val: bytes):  # DONT USE IT TO CREATE LONG BV!!
    res = None
    for c in val:
        v = BVV(c, 8)
        res = res.Concat(v) if res is not None else v
    return res


def split_bv(bv: BV, split_index: int):
    return (
        bv.Extract(bv.size - 1, split_index),  # most significant
        bv.Extract(split_index - 1, 0)         # least significant
    )


def symbolic(val: BV) -> bool:
    return not isinstance(val, BVV)


def heuristic_find_base(val: BV):  # this can be brough inside BVExpr
    z3val = val.z3obj
    fringe = z3val.children()
    while fringe:
        el = fringe.pop()
        if (
            not (z3.simplify(z3val).decl().kind() != z3.Z3_OP_BNUM) and
            el.value > MIN_BASE
        ):
            return el.value
        fringe.extend(el.children())
    return -1
