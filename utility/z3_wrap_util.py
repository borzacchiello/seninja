import z3

MIN_BASE = 0x10000

def bvs(name: str, size: int):
    return z3.BitVec(name, size)

def bvv(val: int, size: int):
    return z3.BitVecVal(val, size)

def split_bv_in_list(bv: z3.BitVecRef, size: int) -> list:
    assert size % 8 == 0
    res = []
    for i in range(0, bv.size, size):
        b = z3.simplify(z3.Extract(i+size-1, i, bv))
        res.append(b)
    return res

def bvv_from_bytes(val: bytes):  # DONT USE IT TO CREATE LONG BV!!
    res = None 
    for c in val: 
        v = z3.BitVecVal(c, 8) 
        res = z3.Concat(res, v) if res is not None else v 
    return res

def split_bv(bv: z3.BitVecRef, split_index: int):
    return (
        z3.simplify(z3.Extract(bv.size - 1, split_index, bv)),  # most significant
        z3.simplify(z3.Extract(split_index - 1, 0, bv))           # least significant
    )

def symbolic(val: z3.BitVecRef) -> bool:
    return z3.simplify(val).decl().kind() != z3.Z3_OP_BNUM

def bvv_to_long(val: z3.BitVecRef):
    assert not symbolic(val)
    return z3.simplify(val).value

def heuristic_find_base(val: z3.BitVecRef):
    fringe = val.children()
    while fringe:
        el = fringe.pop()
        if not symbolic(el) and el.value > MIN_BASE:
            return el.value
        fringe.extend(el.children())
    return -1
