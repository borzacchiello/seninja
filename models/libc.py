from sym_state import State
from utility.z3_wrap_util import symbolic, bvv, bvs
from utility.models_util import get_arg_k
from memory.sym_memory import InitData
from options import ATOX_SLOW_MODEL, MAX_MALLOC
import re
import z3

ascii_numbers = ["0","1","2","3","4","5","6","7","8","9"]

def printf_handler(state: State, view):  # TODO think about stdout
    format_str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    assert not symbolic(format_str_p) or not state.solver.symbolic(format_str_p)

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.as_long() != 0:
        format_str   += chr(b.as_long())
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)

    state.events.append(
        "printf with format '%s'" % format_str
    )

    return bvv(len(format_str), 32)

getchar_count = 0
def getchar_handler(state: State, view):
    global getchar_count
    new_symb = z3.BitVec("getchar_symb_%d" % getchar_count, 8)
    getchar_count += 1

    state.events.append(
        "getchar called"
    )
    state.os.get_stdin().append(new_symb)

    return new_symb

scanf_count = 0
def scanf_handler(state: State, view):
    global scanf_count
    format_str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    assert not symbolic(format_str_p) or not state.solver.symbolic(format_str_p)

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.as_long() != 0:
        format_str   += chr(b.as_long())
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)
    
    state.events.append(
        "scanf with format '%s'" % format_str
    )
    params = re.findall("%([0-9]*s|d|x)", format_str)  # TODO generalize

    i = 2
    for p in params:

        par_p = get_arg_k(state, i, state.arch.bits() // 8, view)
        assert not symbolic(par_p) or not state.solver.symbolic(par_p)
        name = 'scanf_input_%d' % scanf_count

        if p[-1] == "d" or p[-1] == "x":
            data = bvs(name + "_INT", 32)
            state.os.get_stdin().append(data)
            state.mem.store(par_p, data, endness=state.arch.endness())
        elif p[-1] == "s":
            n = 40
            if p[0] != "s":
                n = int(p[:-1])

            data = bvs(name + "_STR", 8*(n - 1))
            state.os.get_stdin().append(z3.Concat(data, bvv(ord("\n"), 8)))
            state.mem.store(par_p, z3.Concat(data, bvv(0, 8)), 'big')
            for i in range(0, data.size(), 8):
                b = z3.Extract(i+7, i, data)
                state.solver.add_constraints(b != ord("\n"))

        scanf_count += 1
        i += 1

    return bvv(1, 32)

def strcmp_handler(state: State, view):
    str1 = get_arg_k(state, 1, state.arch.bits() // 8, view)
    str2 = get_arg_k(state, 2, state.arch.bits() // 8, view)

    assert not symbolic(str1) or not state.solver.symbolic(str1)
    assert not symbolic(str2) or not state.solver.symbolic(str2)

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
    
    return z3.simplify(z3.If(cond, bvv(0, 32), bvv(1, 32)))

def strlen_handler(state: State, view):
    str1 = get_arg_k(state, 1, state.arch.bits() // 8, view)

    assert not symbolic(str1) or not state.solver.symbolic(str1)

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
    res = bvv(i, state.arch.bits())
    for i, b in vals[::-1]:
        res = z3.simplify(z3.If(b == 0, bvv(i, state.arch.bits()), res))
    return z3.simplify(res)

# ************** atoX models **************

# SLOW... but cool :)
atox_idx = 0
def _atox(state: State, view, size: int):
    if not ATOX_SLOW_MODEL:
        global atox_idx
        atox_idx += 1
        return bvs('atox_unconstrained_{idx}'.format(atox_idx), size*8)

    input_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    # no man. Don't make me cry
    assert not symbolic(input_p) or not state.solver.symbolic(input_p)

    def build_or_expression(b):
        conditions = []
        for n in ascii_numbers:
            n = ord(n)
            conditions.append(b == n)
        return z3.Or(*conditions)

    max_len = len(str(2**(size * 8)))  # max valid number

    first_char = state.mem.load(input_p, 1)
    state.solver.add_constraints(
        build_or_expression(first_char)
    )  # first char must be ascii

    i     = 1
    char  = state.mem.load(input_p + i, 1)
    chars = []
    while i <= max_len:

        cond_1 = build_or_expression(char)
        cond_2 = char == 0
        cond_3 = z3.BoolVal(False)
        for old_char in chars:
            cond_2 = z3.And(
                cond_2,
                old_char != 0
            )
            cond_3 = z3.Or(
                cond_3,
                old_char == 0
            )
        cond = z3.Or(
            cond_1, cond_2, cond_3
        )
        state.solver.add_constraints(
            cond
        )

        chars.append(char)
        i+=1
        char = state.mem.load(input_p + i, 1)
        
    chars = [first_char] + chars
    
    # one bit more, to prevent overflow
    res = z3.ZeroExt(size*8+1-8, first_char) - ord('0')
    for i in range(len(chars)-1, 0, -1):
        char = chars[i]

        expr = None
        for j in range(len(chars[:i])):
            # one bit more, to prevent overflow
            old_char = z3.ZeroExt(size*8+1-8, chars[i-j-1])
            if expr is not None:
                expr += (10**j)*(old_char - ord('0'))
            else:
                expr  = (10**j)*(old_char - ord('0'))

        res = z3.If(
            char == 0,
                expr,
                res
            )

    # prevent overflow
    overflow_bit = z3.Extract(size*8, size*8, res)
    state.solver.add_constraints(
        overflow_bit == 0
    )

    assert state.solver.satisfiable()
    return z3.simplify(z3.Extract(size*8-1, 0, res))

def atoi_handler(state: State, view): 
    return _atox(state, view, 4)

def atol_handler(state: State, view):
    return _atox(state, view, 8)

# ********* MALLOC MODELS *********

def malloc_handler(state: State, view):
    size = get_arg_k(state, 1, 4, view)
    if symbolic(size):
        size = state.solver.max(size)
        if size > MAX_MALLOC:
            size = MAX_MALLOC
    else:
        size = size.as_long()
    
    res = state.mem.allocate(size)
    return bvv(res, state.arch.bits())

def calloc_handler(state: State, view):
    size = get_arg_k(state, 1, 4, view)
    if symbolic(size):
        size = state.solver.max(size)
        if size > MAX_MALLOC:
            size = MAX_MALLOC
    else:
        size = size.as_long()
    
    res = state.mem.allocate(
        size,
        InitData(bytes="\x00"*size, index=0)
    )
    return bvv(res, state.arch.bits())

# ***************************************