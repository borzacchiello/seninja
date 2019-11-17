from sym_state import State
from utility.z3_wrap_util import symbolic, bvv, bvs
from utility.models_util import get_arg_k
import z3

time_idx = 0
def time_handler(state: State, view):
    global time_idx
    res = bvs("time_%d" % time_idx, state.arch.bits())

    return res

pid_cache = None
def getpid_handler(state: State, view):
    res = pid_cache if pid_cache else bvs('pid_symb', 32)

    return res
