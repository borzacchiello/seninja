from ..expr import BV, BVV, And, Or
from .expr_wrap_util import split_bv_in_list


def str_to_int(s):
    res = ""
    for c in s:
        res += hex(ord(c))[2:]
    res += "00"
    return int(res, 16)


def str_to_bv_list(s, terminator=False):
    res = list()
    for c in s:
        res.append(BVV(ord(c), 8))
    if terminator:
        res += [BVV(0, 8)]
    return res


def str_to_bv(s, terminator=False):
    if len(s) == 0:
        return None

    res = BVV(ord(s[0]), 8)
    for c in s[1:]:
        res = res.Concat(BVV(ord(c), 8))
    if terminator:
        res = res.Concat(BVV(0, 8))
    return res


def int_to_str(i):
    s = hex(i)[2:]
    res = ""
    for i in range(0, len(s), 2):
        res += chr(int(s[i] + s[i+1], 16))
    return res


def as_bytes(bv: BV):
    for i in range(bv.size, 0, -8):
        yield bv.Extract(i-1, i-8)


def get_byte(bv: BV, i: int):
    return bv.Extract(bv.size-i*8-1, bv.size-i*8-8)


def constraint_alphanumeric_string(bv, state):
    for bv in split_bv_in_list(bv, 8):
        state.solver.add_constraints(
            Or(
                And(bv >= ord("a"), bv <= ord("z")),
                And(bv >= ord("A"), bv <= ord("Z")),
                And(bv >= ord("0"), bv <= ord("9"))
            )
        )


def constraint_ascii_string(bv, state):
    for bv in split_bv_in_list(bv, 8):
        state.solver.add_constraints(
            bv >= 0x20, bv <= 0x7E
        )
