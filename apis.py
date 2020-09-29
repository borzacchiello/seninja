import seninja.seninja_globals as globs
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


def __check_executor():
    if globs.executor is None:
        log_alert("seninja not running")
        return False
    return True


def start_se(bv, address):
    if globs.executor is not None:
        log_alert("seninja is already running")
        return False
    globs.executor = SymbolicExecutor(bv, address)
    globs.dfs_searcher = searcher.DFSSearcher(globs.executor)
    globs.bfs_searcher = searcher.BFSSearcher(globs.executor)


def continue_until_branch():
    if not __check_executor():
        return

    k = globs.executor.fringe.last_added
    i = k
    while not globs._stop and i == k:
        globs.executor.execute_one()
        if not globs.executor.state:
            break
        i = globs.executor.fringe.last_added

    globs._stop = False
    return globs.executor.state, globs.executor.fringe.last_added


def continue_until_address(address):
    ip = globs.executor.state.get_ip()

    while ip != address:
        globs.executor.execute_one()
        if not globs.executor.state:
            break
        ip = globs.executor.state.get_ip()

    return globs.executor.state


def run_dfs(target: int, avoid: list = None):
    if not __check_executor():
        return

    def callback(s):
        if globs._stop:
            globs._stop = False
            return False
        return True

    dfs_s = searcher.DFSSearcher(globs.executor)
    dfs_s.set_target(target)
    if avoid is not None:
        for a in avoid:
            dfs_s.add_avoid(a)

    res = dfs_s.run(callback)
    return res


def run_bfs(target: int, avoid: list = None):
    if not __check_executor():
        return

    def callback(s):
        if globs._stop:
            globs._stop = False
            return False
        return True

    bfs_s = searcher.BFSSearcher(globs.executor)
    bfs_s.set_target(target)
    if avoid is not None:
        for a in avoid:
            bfs_s.add_avoid(a)

    res = bfs_s.run(callback)
    return res


def execute_one_instruction(bv):
    if not __check_executor():
        return

    globs.executor.execute_one()

    return globs.executor.state


def change_current_state(address_or_state):
    # take only the first one at the given address. TODO
    if not __check_executor():
        return

    if not isinstance(address_or_state, State):
        state = globs.executor.fringe.get_deferred_by_address(address_or_state)
    else:
        state = address_or_state
    if state is None:
        log_alert("no such deferred state")
        return

    globs.executor.set_current_state(state)


def focus_current_state(bv):
    if not __check_executor():
        return
    bv.file.navigate(bv.file.view, globs.executor.state.get_ip())


def setup_argv(*args, argc_loc=None, argv_loc=None):
    if not __check_executor():
        return

    filename = globs.executor.view.file.filename
    state = globs.executor.state
    argv_p = BVV(state.mem.allocate((len(args) + 1) *
                                    (state.arch.bits() // 8)), state.arch.bits())
    argv_1_p = BVV(state.mem.allocate(len(filename)), state.arch.bits())
    for i, b in enumerate(str_to_bv_list(filename, terminator=True)):
        state.mem.store(argv_1_p + i, b)
    state.mem.store(argv_p, argv_1_p, state.arch.endness())

    for i, arg in enumerate(args):
        if not isinstance(arg, BV):
            print("ERROR: %s is not a BitVector" % str(arg))
            return
        argv_el_p = BVV(state.mem.allocate(
            arg.size // 8 + 1), state.arch.bits())
        state.mem.store(argv_el_p, arg)
        state.mem.store(argv_p + (i + 1) *
                        (state.arch.bits() // 8), argv_el_p, state.arch.endness())

    argc = BVV(len(args) + 1, state.arch.bits())
    if argc_loc is None:
        current_function = globs.executor.bncache.get_function(
            globs.executor.ip)
        argc_loc = current_function.calling_convention.int_arg_regs[0]

    if isinstance(argc_loc, str):
        setattr(state.regs, argc_loc, argc)
    elif isinstance(argc_loc, BV):
        state.mem.store(argc_loc, argc, state.arch.endness())
    else:
        print("ERROR: invalid argc_loc %s" % str(argc_loc))
        return

    if argv_loc is None:
        current_function = globs.executor.bncache.get_function(
            globs.executor.ip)
        argv_loc = current_function.calling_convention.int_arg_regs[1]

    if isinstance(argv_loc, str):
        setattr(state.regs, argv_loc, argv_p)
    elif isinstance(argv_loc, BV):
        state.mem.store(argv_loc, argv_p, state.arch.endness())
    else:
        print("ERROR: invalid argv_loc %s" % str(argv_loc))
        return


def constraint_bv(bv_list: list, pattern: str):
    if not __check_executor():
        return

    state = globs.executor.state
    for bv in bv_list:
        assert bv.size == 8

        expr = Or(*list(map(lambda x: bv == BVV(x, 8), pattern)))
        state.solver.add_constraints(
            expr
        )


def reset_se(bv=None):
    if not __check_executor():
        return

    globs.executor.reset()
    globs.executor = None


def stop():
    if globs._running:  # race conditions?
        globs._stop = True


def get_current_state():
    if not __check_executor():
        return None

    return globs.executor.state


def get_executor():
    if not __check_executor():
        return None

    return globs.executor


def mk_symb_buffer(state, name, size):
    buff = BVS(name, size * 8)
    address = state.mem.allocate(size)
    state.mem.store(address, buff)
    state.symbolic_buffers.append(
        (buff, address, "")
    )
    return buff


def register_hook(address, func):
    if not __check_executor():
        return

    globs.executor.user_hooks[address] = func


def register_logger(address, func):
    if not __check_executor():
        return

    globs.executor.user_loggers[address] = func


def reload_settings():
    if not __check_executor():
        return

    globs.executor.bncache.settings = {}
