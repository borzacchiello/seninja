from binaryninja import (
    log_alert,
    log_info,
    BackgroundTaskThread,
    PluginCommand
)
from .sym_executor import SymbolicExecutor
from .multipath import searcher
from .sym_state import State
from .models import function_models as seninja_models
from .expr import BVV, BVS, BV, And, Or, ITE
from .utility.string_util import (
    int_to_str,
    str_to_int,
    as_bytes,
    get_byte,
    str_to_bv_list,
    str_to_bv
)
from .utility.expr_wrap_util import split_bv_in_list
from .utility.bninja_util import get_address_after_merge
from .globals import Globals

def get_current_state():
    if not Globals.uimanager.symbolic_started():
        return None
    return Globals.uimanager.executor.state

def constraint_bv(bv_list: list, pattern: str):
    state = get_current_state()
    if state is None:
        return

    for bv in bv_list:
        assert bv.size == 8

        expr = Or(*list(map(lambda x: bv == BVV(x, 8), pattern)))
        state.solver.add_constraints(
            expr
        )

def mk_symb_buffer(state, name, size):
    buff = BVS(name, size * 8)
    address = state.mem.allocate(size)
    state.mem.store(address, buff)
    state.symbolic_buffers.append(
        (buff, address, "")
    )
    return buff

def get_stdin_bv(state):
    r = None
    for el in state.os.get_stdin_stream():
        if r is None:
            r = el
        else:
            r = r.Concat(el)
    return r

def get_stdout_bv(state):
    r = None
    for el in state.os.get_stdout_stream():
        if r is None:
            r = el
        else:
            r = r.Concat(el)
    return r

def register_hook(address, func):
    if not Globals.uimanager.symbolic_started():
        return
    Globals.uimanager.executor.user_hooks[address] = func


def register_logger(address, func):
    if not Globals.uimanager.symbolic_started():
        return
    Globals.uimanager.executor.user_loggers[address] = func


def reload_settings():
    if not Globals.uimanager.symbolic_started():
        return
    Globals.uimanager.executor.bncache.settings = {}
