from sym_state import State
from utility.z3_wrap_util import symbolic, bvv, bvs
from utility.models_util import get_arg_k
import z3

ascii_numbers = ["0","1","2","3","4","5","6","7","8","9"]

# just pseudo-stubs... Don't take them seriously

def printf_handler(state: State, view): 
    format_str_p = get_arg_k(state, 1, view)
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

def scanf_handler(state: State, view):
    format_str_p = get_arg_k(state, 1, view)

    assert not symbolic(format_str_p)

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.as_long() != 0:
        format_str   += chr(b.as_long())
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)
    
    assert format_str.count("%s") == 1 and format_str.count("%") == 1  # TODO generalize

    par_p = get_arg_k(state, 2, view)

    assert not symbolic(par_p)

    data = bvs('scanf_input', 8*40)
    state.mem.store(par_p, data, 'big')
    state.solver.add_constraints(state.mem.load(par_p + 39, 1) == 0)
    return bvv(40, 32)

def strcmp_handler(state: State, view):
    str1 = get_arg_k(state, 1, view)
    str2 = get_arg_k(state, 2, view)

    assert not symbolic(str1)
    assert not symbolic(str2)

    b1 = state.mem.load(str1, 1)
    b2 = state.mem.load(str2, 1)
    cond = z3.BoolVal(True)
    i = 0
    while i < 40:
        if not state.solver.symbolic(b1) and state.solver.evaluate_long(b1) == 0:
            break
        if not state.solver.symbolic(b2) and state.solver.evaluate_long(b2) == 0:
            break
        cond = z3.And(b1 == b2, cond)
        str1 += 1
        str2 += 1
        b1 = state.mem.load(str1, 1)
        b2 = state.mem.load(str2, 1)
        i += 1
    
    return z3.If(cond, bvv(0, 32), bvv(1, 32))

def strlen_handler(state: State, view):
    str1 = get_arg_k(state, 1, view)

    assert not symbolic(str1)

    b1 = state.mem.load(str1, 1)
    vals = []
    i = 0
    while i < 40:
        if not state.solver.symbolic(b1) and state.solver.evaluate_long(b1) == 0:
            break
        
        vals.append((i, b1))
        i += 1
        str1 += 1
        b1 = state.mem.load(str1, 1)
    
    state.solver.add_constraints(b1 == 0)
    res = bvv(i, 32)
    for i, b in vals[::-1]:
        res = z3.simplify(z3.If(b == 0, bvv(i, 32), res))
    return res

def atoi_handler(state: State, view): 
    # TODO broken
    input_p = get_arg_k(state, 1, view)

    assert not symbolic(input_p) and not state.solver.symbolic(input_p)  # no man. Don't make me cry

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
