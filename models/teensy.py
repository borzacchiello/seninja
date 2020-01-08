from ..sym_state import State
from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS
from ..utility.models_util import get_arg_k

def println_handler(state: State, view):
    to_print = get_arg_k(state, 0, state.arch.bits() // 8, view)
    state.events.append(
        "println called with parameter: {to_print}".format(
            to_print = to_print
        )
    )
    return BVV(0, 32)
