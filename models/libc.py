from sym_state import State
from utility.expr_wrap_util import symbolic
from expr import BVV, BVS, BoolV, ITE, Or, And
from utility.models_util import get_arg_k
from utility.string_util import as_bytes, str_to_bv_list
from memory.sym_memory import InitData
from options import ATOX_SLOW_MODEL, MAX_MALLOC, MAX_SYMB_STR
import re

ascii_numbers = ["0","1","2","3","4","5","6","7","8","9"]

def _intbv_to_strbv16(intbv):
    # int bv to string bv in hex
    res = [BVV(ord("0"), 8), BVV("x", 8)]
    for b in as_bytes(intbv):
        low = b.Extract(3, 0).ZeroExt(4)
        hig = b.Extract(7, 4).ZeroExt(4)

        rb_low = ITE(
            low.ULT(10),
            BVV(ord("0"), 8) + low,
            BVV(ord("A"), 8) - 10 + low
        )
        rb_hig = ITE(
            hig.ULT(10),
            BVV(ord("0"), 8) + hig,
            BVV(ord("A"), 8) - 10 + hig
        )
        v = rb_hig.Concat(rb_low)
        res.append(v)
    
    return res

def printf_handler(state: State, view):  # only concrete
    format_str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    assert not symbolic(format_str_p) or not state.solver.symbolic(format_str_p)

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.value != 0:
        format_str   += chr(b.value)
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)

    state.events.append(
        "printf with format '%s'" % format_str
    )

    res = list()
    last_idx = 0
    param_idx = 2
    params = re.finditer("%([0-9]*s|d|x|c)", format_str)  # TODO generalize
    for param in params:
        index = param.start()
        match = param.group()

        val = list()
        if match[-1] == "s":
            # string
            param_p = get_arg_k(state, param_idx, state.arch.bits() // 8, view)
            l = int(match[1:-1]) if len(match) > 2 else MAX_SYMB_STR

            i = 0
            c = state.mem.load(param_p, 1)
            while i < l:
                if not symbolic(c) and c.value == 0:
                    break
                val.append(c)
                param_p += 1
                c = state.mem.load(param_p, 1)
                i += 1

        elif match == "%d" or match == "%x":
            int_val = get_arg_k(state, param_idx, 4, view)

            val = _intbv_to_strbv16(int_val)

        elif match == "%c":
            c = get_arg_k(state, param_idx, 1, view)

            val = [c]

        param_idx += 1

        format_substr = format_str[last_idx:index]
        last_idx = index + len(match)
        res.extend(str_to_bv_list(format_substr))
        res.extend(val)
    
    format_substr = format_str[last_idx:]
    res.extend(str_to_bv_list(format_substr))

    state.os.get_stdout().extend(res)
    return BVV(len(res), 32)

getchar_count = 0
def getchar_handler(state: State, view):
    global getchar_count
    new_symb = BVS("getchar_symb_%d" % getchar_count, 8)
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
    while not symbolic(b) and b.value != 0:
        format_str   += chr(b.value)
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
            data = BVS(name + "_INT", 32)
            state.os.get_stdin().append(data)
            state.mem.store(par_p, data, endness=state.arch.endness())
        elif p[-1] == "s":
            n = 40
            if p[0] != "s":
                n = int(p[:-1])

            data = BVS(name + "_STR", 8*(n - 1))
            state.os.get_stdin().append(data.Concat(BVV(ord("\n"), 8)))
            state.mem.store(par_p, data.Concat(BVV(0, 8)), 'big')
            for i in range(0, data.size, 8):
                b = data.Extract(i+7, i)
                state.solver.add_constraints(b != ord("\n"))

        scanf_count += 1
        i += 1

    return BVV(1, 32)

def strcmp_handler(state: State, view):
    str1 = get_arg_k(state, 1, state.arch.bits() // 8, view)
    str2 = get_arg_k(state, 2, state.arch.bits() // 8, view)

    assert not symbolic(str1) or not state.solver.symbolic(str1)
    assert not symbolic(str2) or not state.solver.symbolic(str2)

    b1 = state.mem.load(str1, 1)
    b2 = state.mem.load(str2, 1)
    cond = BoolV(True)
    i = 0
    while i < 40:
        if not state.solver.symbolic(b1) and state.solver.evaluate(b1).value == 0:
            break
        if not state.solver.symbolic(b2) and state.solver.evaluate(b2).value == 0:
            break
        cond = (b1 == b2).And(cond)
        str1 += 1
        str2 += 1
        b1 = state.mem.load(str1, 1)
        b2 = state.mem.load(str2, 1)
        i += 1
    
    return ITE(cond, BVV(0, 32), BVV(1, 32))

def strlen_handler(state: State, view):
    str1 = get_arg_k(state, 1, state.arch.bits() // 8, view)

    assert not symbolic(str1) or not state.solver.symbolic(str1)

    b1 = state.mem.load(str1, 1)
    vals = []
    i = 0
    while i < 40:
        if not state.solver.symbolic(b1) and state.solver.evaluate(b1).value == 0:
            break
        
        vals.append((i, b1))
        i += 1
        str1 += 1
        b1 = state.mem.load(str1, 1)
    
    state.solver.add_constraints(b1 == 0)
    res = BVV(i, state.arch.bits())
    for i, b in vals[::-1]:
        res = ITE(b == 0, BVV(i, state.arch.bits()), res)
    return res

# ************** atoX models **************

# SLOW... but cool :)
atox_idx = 0
def _atox(state: State, view, size: int):
    if not ATOX_SLOW_MODEL:
        global atox_idx
        atox_idx += 1
        return BVS('atox_unconstrained_{idx}'.format(atox_idx), size*8)

    input_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    # no man. Don't make me cry
    assert not symbolic(input_p) or not state.solver.symbolic(input_p)

    def build_or_expression(b):
        conditions = []
        for n in ascii_numbers:
            n = ord(n)
            conditions.append(b == n)
        return Or(*conditions)

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
        cond_3 = BoolV(False)
        for old_char in chars:
            cond_2 = And(
                cond_2,
                old_char != 0
            )
            cond_3 = Or(
                cond_3,
                old_char == 0
            )
        cond = Or(
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
    res = first_char.ZeroExt(size*8+1-8) - ord('0')
    for i in range(len(chars)-1, 0, -1):
        char = chars[i]

        expr = None
        for j in range(len(chars[:i])):
            # one bit more, to prevent overflow
            old_char = chars[i-j-1].ZeroExt(size*8+1-8)
            if expr is not None:
                expr += (10**j)*(old_char - ord('0'))
            else:
                expr  = (10**j)*(old_char - ord('0'))

        res = ITE(
            char == 0,
                expr,
                res
            )

    # prevent overflow
    overflow_bit = res.Extract(size*8, size*8)
    state.solver.add_constraints(
        overflow_bit == 0
    )

    assert state.solver.satisfiable()
    return res.Extract(size*8-1, 0)

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
        size = size.value
    
    res = state.mem.allocate(size)
    return BVV(res, state.arch.bits())

def calloc_handler(state: State, view):
    size = get_arg_k(state, 1, 4, view)
    if symbolic(size):
        size = state.solver.max(size)
        if size > MAX_MALLOC:
            size = MAX_MALLOC
    else:
        size = size.value
    
    res = state.mem.allocate(
        size,
        InitData(bytes="\x00"*size, index=0)
    )
    return BVV(res, state.arch.bits())

# ***************************************