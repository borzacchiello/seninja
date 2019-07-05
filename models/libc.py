from sym_state import State
from utility.z3_wrap_util import symbolic, bvv
from utility.models_util import get_arg_k
import z3

ascii_numbers = ["0","1","2","3","4","5","6","7","8","9"]

# just pseudo-stubs... Don't take them seriously

def printf_handler(state: State): 
    format_str_p = get_arg_k(state, 1)
    
    assert not symbolic(format_str_p)

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.as_long() != 0:
        format_str   += chr(b.as_long())
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)

    state.events.append(
        "printf with format '%s'" % (format_str)
    )

    return bvv(len(format_str), 32)

def atoi_handler(state: State):
    # TODO broken
    input_p = get_arg_k(state, 1)

    assert not symbolic(input_p)  # no man. Don't make me cry

    def build_or_expression(b):
        conditions = []
        for n in ascii_numbers:
            n = ord(n)
            conditions.append(b == n)
        return z3.Or(*conditions)

    max_len = 10
    i = 0
    b = state.mem.load(input_p + i, 1)
    array = None
    while i < max_len and state.solver.evaluate_long(b) != ord("\n"):
        array = z3.Concat(b, array) if array is not None else b
        if symbolic(b):
            state.solver.add_constraints(build_or_expression(b))
        i += 1
        b = state.mem.load(input_p + i, 1)
    if symbolic(b):
        state.solver.add_constraints(b == ord("\n"))
    
    assert state.solver.satisfiable()  # we should create an errored state...
    assert array.size() % 8 == 0  # load 8 bytes at a time...

    res = bvv(0, 32)
    for i in range(0, array.size(), 8):
        b = z3.ZeroExt(32-8, z3.Extract(i+7, i, array))
        res = (res + (b - ord("0")) * (10 ** (i // 8)))
    
    return res
