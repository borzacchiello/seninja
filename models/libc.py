from ..sym_state import State
from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS, BoolV, ITE, Or, And
from ..utility.models_util import get_arg_k
from ..utility.exceptions import ExitException, ModelError
from ..utility.string_util import as_bytes, str_to_bv_list
from ..memory.sym_memory import InitData
import re
import os
import ctypes
import ctypes.util

if os.name == 'nt':
    # windows
    libc_native_path = ctypes.util.find_library('msvcrt')
else:
    libc_native_path = ctypes.util.find_library('c')
libc_native = ctypes.cdll.LoadLibrary(libc_native_path)
ascii_numbers = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

# ---- NATIVE CONCRETE HANDLERS -----

def srand_handler(state: State, view):
    seed = get_arg_k(state, 1, state.arch.bits() // 8, view)
    libc_native.srand(seed.value)
    return BVV(1, 32)

def rand_handler(state: State, view):
    val = libc_native.rand()
    return BVV(val, 32)

def strtoul_handler(state: State, view):
    str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)
    endptr = get_arg_k(state, 2, state.arch.bits() // 8, view)
    base = get_arg_k(state, 3, 4, view)

    if symbolic(base) or symbolic(endptr) or symbolic(str_p):
        raise ModelError("strtoul", "symbolic arguments are not supported")

    i = 0
    str_data = b""
    b = state.mem.load(str_p, 1)
    while not symbolic(b) and i < 64:
        b = b.value
        str_data += bytes([b])
        if b == 0:
            break
        i += 1
        b = state.mem.load(str_p + i, 1)

    _native_buff = ctypes.c_char_p(str_data)
    _native_endptr = ctypes.c_ulong(0)
    _native_base = base.value

    _native_res = libc_native.strtoul(
        _native_buff,
        ctypes.byref(_native_endptr),
        _native_base
    )

    offset = (_native_endptr.value & 0xffffffff) - \
        (ctypes.cast(_native_buff, ctypes.c_void_p).value & 0xffffffff)
    assert offset >= 0
    state.mem.store(endptr, BVV((str_p.value + offset),
                                state.arch.bits()), 'little')
    return BVV(_native_res, state.arch.bits())
# -----------------------------------


def exit_handler(state: State, view):
    raise ExitException()


def _intbv_to_strbv16(intbv):
    # int bv to string bv in hex
    res = [BVV(ord("0"), 8), BVV(ord("x"), 8)]
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
        v = [rb_hig, rb_low]
        res.extend(v)

    return res


def _printf_common(state: State, format_str_p, param_idx_start, view):
    if symbolic(format_str_p) and state.solver.symbolic(format_str_p):
        raise ModelError("_printf_common", "symbolic format string not supported")

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.value != 0:
        format_str += chr(b.value)
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)

    state.events.append(
        "printf with format '%s'" % format_str
    )

    match = ""
    res = list()
    last_idx = 0
    param_idx = param_idx_start
    params = re.finditer("%([0-9]*s|d|u|x|X|c)", format_str)  # TODO generalize
    for param in params:
        index = param.start()
        match = param.group()

        val = list()
        if match[-1] == "s":
            # string
            param_p = get_arg_k(state, param_idx, state.arch.bits() // 8, view)
            max_symb_str = int(state.executor.bncache.get_setting(
                "models.max_size_symb_string"))
            l = int(match[1:-1]) if len(match) > 2 else max_symb_str

            i = 0
            c = state.mem.load(param_p, 1)
            while i < l:
                if not symbolic(c) and c.value == 0:
                    break
                val.append(c)
                param_p += 1
                c = state.mem.load(param_p, 1)
                i += 1

        elif match == "%d" or match == "%u" or match == "%x" or match == "%X":
            int_val = get_arg_k(state, param_idx, 4, view)
            if symbolic(int_val):
                val = _intbv_to_strbv16(int_val)
            else:
                if match == "%d" or match == "%u":
                    val = str_to_bv_list(str(int_val.value))
                else:
                    val = str_to_bv_list(hex(int_val.value)[2:])

        elif match == "%c":
            c = get_arg_k(state, param_idx, 1, view)

            val = [c]

        param_idx += 1

        format_substr = format_str[last_idx:index]
        last_idx = index + len(match)
        res.extend(str_to_bv_list(format_substr))
        res.extend(val)

    format_substr = format_str[last_idx + len(match):]
    res.extend(str_to_bv_list(format_substr))

    return res, BVV(len(res), 32)


def printf_handler(state: State, view):  # only concrete
    format_str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)
    data_list, res_n = _printf_common(state, format_str_p, 2, view)

    state.os.write(state.os.stdout_fd, data_list)
    return res_n


def printf_chk_handler(state: State, view):
    flag = get_arg_k(state, 1, 4, view)  # TODO ignored
    format_str_p = get_arg_k(state, 2, state.arch.bits() // 8, view)
    data_list, res_n = _printf_common(state, format_str_p, 3, view)

    state.os.write(state.os.stdout_fd, data_list)
    return res_n


def putchar_handler(state: State, view):
    res = get_arg_k(state, 1, 4, view)
    c = res.Extract(7, 0)

    state.os.write(state.os.stdout_fd, [c])
    return res


def puts_handler(state: State, view):
    string_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    max_symb_str = int(state.executor.bncache.get_setting(
        "models.max_size_symb_string"))
    i = 0
    c = state.mem.load(string_p, 1)
    while (not symbolic(c) and c.value != 0) or (symbolic(c) and i < max_symb_str):
        state.os.write(state.os.stdout_fd, [c])
        i += 1
        c = state.mem.load(string_p + i, 1)

    return BVV(0, 32)


def getchar_handler(state: State, view):
    state.events.append(
        "getchar called"
    )

    v = state.os.read(state.os.stdin_fd, 1)
    return v[0]


scanf_count = 0


def scanf_handler(state: State, view):
    # scanf does not support reading data from stdin... Too difficult to model
    # it will simply write on stdin the correct data
    global scanf_count
    format_str_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    if symbolic(format_str_p) and state.solver.symbolic(format_str_p):
        raise ModelError("scanf_handler", "symbolic format string not supported")

    b = state.mem.load(format_str_p, 1)
    format_str = ""
    while not symbolic(b) and b.value != 0:
        format_str += chr(b.value)
        format_str_p += 1
        b = state.mem.load(format_str_p, 1)

    state.events.append(
        "scanf with format '%s'" % format_str
    )

    match = ""
    bytes_read = list()
    last_idx = 0
    param_idx = 2
    params = re.finditer("%([0-9]*s|d|x)", format_str)  # TODO generalize
    for param in params:
        index = param.start()
        match = param.group()

        tmp_bytes_red = list()
        par_p = get_arg_k(state, param_idx, state.arch.bits() // 8, view)
        if symbolic(par_p) and state.solver.symbolic(par_p):
            raise ModelError("scanf_handler", "symbolic pointer for arguments not supported")
        name = 'scanf_input_%d' % scanf_count

        if match[-1] == "d" or match[-1] == "x":
            data = BVS(name + "_INT", 32)
            state.mem.store(par_p, data, endness=state.arch.endness())
            tmp_bytes_red = _intbv_to_strbv16(data)
        elif match[-1] == "s":
            max_symb_str = int(state.executor.bncache.get_setting(
                "models.max_size_symb_string"))
            n = int(match[1:-1]) if len(match) > 2 else max_symb_str

            data = BVS(name + "_STR", 8*(n - 1))
            state.mem.store(par_p, data.Concat(BVV(0, 8)), 'big')
            for i in range(0, data.size, 8):
                b = data.Extract(i+7, i)
                state.solver.add_constraints(b != ord("\n"))
                tmp_bytes_red.append(b)

        param_idx += 1

        format_substr = format_str[last_idx:index]
        last_idx = index + len(match)
        bytes_read.extend(str_to_bv_list(format_substr))
        bytes_read.extend(tmp_bytes_red)

        scanf_count += 1

    format_substr = format_str[last_idx + len(match):]
    bytes_read.extend(str_to_bv_list(format_substr))
    state.os.write(state.os.stdin_fd, bytes_read)
    return BVV(1, 32)


def fgets_handler(state: State, view):
    s_p = get_arg_k(state, 1, state.arch.bits() // 8, view)
    size = get_arg_k(state, 2, 4, view)
    if symbolic(size):
        actual_size = state.solver.max(size)
        max_size = state.executor.bncache.get_setting(
            "models.max_size_symb_string")

        if actual_size > max_size:
            actual_size = max_size
            state.solver.add_constraints(size == actual_size)
    else:
        actual_size = size.value

    for i in range(actual_size):
        # TODO get correct FD
        v = state.os.read(state.os.stdin_fd, 1)[0]
        state.mem.store(s_p + i, v)
    state.mem.store(s_p + actual_size, BVV(0, 8))

    return s_p


def isxdigit_handler(state: State, view):
    c = get_arg_k(state, 1, 4, view)

    res = ITE(
        Or(
            And(c >= 48, c <= 57),  # 0 -> 9
            And(c >= 97, c <= 102),  # a -> f
            And(c >= 65, c <= 70)   # A -> F
        ), BVV(1, 32), BVV(0, 32)
    )
    return res

# ************** atoX models **************


# SLOW... but cool :)
atox_idx = 0


def _atox(state: State, view, size: int):
    atox_slow_model = state.executor.bncache.get_setting(
        "models.use_atox_slow_model") == 'true'
    if not atox_slow_model:
        global atox_idx
        atox_idx += 1
        return BVS('atox_unconstrained_{idx}'.format(atox_idx), size*8)

    input_p = get_arg_k(state, 1, state.arch.bits() // 8, view)

    if symbolic(input_p) and state.solver.symbolic(input_p):
        # FIXME: I should:
        #            1. return a fresh new symbol
        #            2. allocate a new buffer with a concrete address
        #            3. store the correct expression in the buffer for consistency
        raise ModelError("atox", "symbolic input pointer (not supported)")

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

    i = 1
    char = state.mem.load(input_p + i, 1)
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
        i += 1
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
                expr = (10**j)*(old_char - ord('0'))

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

    if not state.solver.satisfiable():
        raise ModelError("_atox", "unsat solver")
    return res.Extract(size*8-1, 0)


def atoi_handler(state: State, view):
    return _atox(state, view, 4)


def atol_handler(state: State, view):
    return _atox(state, view, 8)

# ********* MALLOC MODELS *********


def malloc_handler(state: State, view):
    size = get_arg_k(state, 1, 4, view)
    max_malloc = int(state.executor.bncache.get_setting(
        "models.max_malloc_size"))
    if symbolic(size):
        size = state.solver.max(size)
        if size > max_malloc:
            size = max_malloc
    else:
        size = size.value

    res = state.mem.allocate(size)
    return BVV(res, state.arch.bits())


def calloc_handler(state: State, view):
    size = get_arg_k(state, 1, 4, view)
    max_malloc = int(state.executor.bncache.get_setting(
        "models.max_malloc_size"))
    if symbolic(size):
        size = state.solver.max(size)
        if size > max_malloc:
            size = max_malloc
    else:
        size = size.value

    res = state.mem.allocate(
        size,
        InitData(bytes=b"\x00"*size, index=0)
    )
    return BVV(res, state.arch.bits())

# ***************************************
