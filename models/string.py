from sym_state import State
from utility.expr_wrap_util import symbolic
from expr import BVV, BVS, BoolV, And, ITE
from utility.models_util import get_arg_k

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
