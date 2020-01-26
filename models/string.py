from ..sym_state import State
from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS, BoolV, And, ITE
from ..utility.models_util import get_arg_k

def memcmp_handler(state: State, view):
    buff1 = get_arg_k(state, 1, state.arch.bits() // 8, view)
    buff2 = get_arg_k(state, 2, state.arch.bits() // 8, view)
    n = get_arg_k(state, 3, state.arch.bits() // 8, view)

    if symbolic(n):
        n = state.solver.max(n)
        max_memcmp = int(state.executor.bncache.get_setting("models.max_memcmp_size"))
        if n > max_memcmp:
            n = max_memcmp
    else:
        n = n.value
    
    res = BoolV(True)
    for i in range(n):
        c1 = state.mem.load(buff1 + i, 1)
        c2 = state.mem.load(buff2 + i, 1)
        
        res = And(
            c1 == c2, res
        )
    
    return ITE(res, BVV(0, 32), BVV(1, 32))

def memset_handler(state: State, view):
    buff = get_arg_k(state, 1, state.arch.bits() // 8, view)
    val  = get_arg_k(state, 2, 1, view)
    n    = get_arg_k(state, 3, 4, view)

    if symbolic(n):
        n = state.solver.max(n)
        max_memset = int(state.executor.bncache.get_setting("models.max_memset_size"))
        if n > max_memset:
            n = max_memset
    else:
        n = n.value
    
    for i in range(n):
        state.mem.store(buff+i, val)
    
    return buff

def strcmp_handler(state: State, view):
    str1 = get_arg_k(state, 1, state.arch.bits() // 8, view)
    str2 = get_arg_k(state, 2, state.arch.bits() // 8, view)

    assert not symbolic(str1) or not state.solver.symbolic(str1)
    assert not symbolic(str2) or not state.solver.symbolic(str2)
    if symbolic(str1):
        str1 = state.solver.evaluate(str1)
    if symbolic(str2):
        str1 = state.solver.evaluate(str2)
    
    max_sym_string = int(state.executor.bncache.get_setting("models.max_size_symb_string"))

    b1 = state.mem.load(str1, 1)
    b2 = state.mem.load(str2, 1)
    cond = BoolV(True)
    i = 0
    while True:
        if not symbolic(b1) or not state.solver.symbolic(b1):
            b1 = state.solver.evaluate(b1) if symbolic(b1) else b1
            if b1.value == 0:
                break
        if not symbolic(b2) or not state.solver.symbolic(b2):
            b2 = state.solver.evaluate(b2) if symbolic(b2) else b2
            if b2.value == 0:
                break
        
        if symbolic(b1) and symbolic(b2) and i > max_sym_string:
            state.solver.add_constraints(b1 == 0, b2 == 0)
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
    if symbolic(str1):
        str1 = state.solver.evaluate(str1)
    
    max_sym_string = int(state.executor.bncache.get_setting("models.max_size_symb_string"))

    b1 = state.mem.load(str1, 1)
    vals = []
    i = 0
    while True:
        if not symbolic(b1) or not state.solver.symbolic(b1):
            b1 = state.solver.evaluate(b1)
            if b1.value == 0:
                break
        elif i > max_sym_string:
            state.solver.add_constraints(b1 == 0)
            break
        
        vals.append((i, b1))
        i += 1
        str1 += 1
        b1 = state.mem.load(str1, 1)
    
    res = BVV(i, state.arch.bits())
    for i, b in vals[::-1]:
        res = ITE(b == 0, BVV(i, state.arch.bits()), res)
    return res

def strcpy_handler(state: State, view):
    dst = get_arg_k(state, 1, state.arch.bits() // 8, view)
    src = get_arg_k(state, 2, state.arch.bits() // 8, view)

    assert not symbolic(dst) or not state.solver.symbolic(dst)
    assert not symbolic(src) or not state.solver.symbolic(src)
    if symbolic(dst):
        dst = state.solver.evaluate(dst)
    if symbolic(src):
        src = state.solver.evaluate(src)
    
    max_sym_string = int(state.executor.bncache.get_setting("models.max_size_symb_string"))
    
    i = 0
    src_b = state.mem.load(src, 1)
    while True:
        if not symbolic(src_b) or not state.solver.symbolic(src_b):
            src_b = state.solver.evaluate(src_b) if symbolic(src_b) else src_b
            if src_b.value == 0:
                break
        elif i > max_sym_string:
            state.solver.add_constraints(src_b == 0)
            break

        state.mem.store(dst + i, src_b)
        i += 1
        src_b = state.mem.load(src + i, 1)

    state.mem.store(dst + i, BVV(0, 8))
    return BVV(i, 32)
