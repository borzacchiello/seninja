from ..sym_state import State
from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS
from ..utility.models_util import get_arg_k

time_idx = 0


def time_handler(state: State, view):
    global time_idx
    res = BVS("time_%d" % time_idx, state.arch.bits())

    return res


pid_cache = None


def getpid_handler(state: State, view):
    res = pid_cache if pid_cache else BVS('pid_symb', 32)

    return res
