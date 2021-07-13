from binaryninja import (
    log_alert,
    log_info
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


class Project(object):
    def __init__(self, bv, addr):
        self.bv = bv
        self.executor = SymbolicExecutor(bv, addr)
        self.dfs_searcher = searcher.DFSSearcher(self.executor)
        self.bfs_searcher = searcher.BFSSearcher(self.executor)

    def get_current_state(self):
        return self.executor.state

    def change_current_state(self, address_or_state):
        if not isinstance(address_or_state, State):
            state = self.executor.fringe.get_deferred_by_address(
                address_or_state)
        else:
            state = address_or_state
        if state is None:
            log_alert("no such deferred state")
            return

        self.executor.set_current_state(state)

    def execute_one_instruction(self):
        self.executor.execute_one()
        return self.executor.state

    def continue_until_branch(self):
        k = self.executor.fringe.last_added
        i = k
        while i == k:
            self.executor.execute_one()
            if not self.executor.state:
                break
            i = self.executor.fringe.last_added

        return self.executor.state, self.executor.fringe.last_added

    def continue_until_address(self, address):
        ip = self.executor.state.get_ip()

        while ip != address:
            self.executor.execute_one()
            if not self.executor.state:
                break
            ip = self.executor.state.get_ip()

        return self.executor.state

    def setup_argv(self, *args, argc_loc=None, argv_loc=None):
        filename = self.bv.file.filename
        state = self.executor.executor.state
        argv_p = BVV(state.mem.allocate((len(args) + 1) *
                                        (state.arch.bits() // 8)), state.arch.bits())
        argv_1_p = BVV(state.mem.allocate(len(filename)), state.arch.bits())
        for i, b in enumerate(str_to_bv_list(filename, terminator=True)):
            state.mem.store(argv_1_p + i, b)
        state.mem.store(argv_p, argv_1_p, state.arch.endness())

        for i, arg in enumerate(args):
            if not isinstance(arg, BV):
                log_alert("ERROR: %s is not a BitVector" % str(arg))
                return
            argv_el_p = BVV(state.mem.allocate(
                arg.size // 8 + 1), state.arch.bits())
            state.mem.store(argv_el_p, arg)
            state.mem.store(argv_p + (i + 1) *
                            (state.arch.bits() // 8), argv_el_p, state.arch.endness())

        argc = BVV(len(args) + 1, state.arch.bits())
        if argc_loc is None:
            current_function = self.executor.bncache.get_function(
                self.executor.ip)
            argc_loc = current_function.calling_convention.int_arg_regs[0]

        if isinstance(argc_loc, str):
            setattr(state.regs, argc_loc, argc)
        elif isinstance(argc_loc, BV):
            state.mem.store(argc_loc, argc, state.arch.endness())
        else:
            log_alert("ERROR: invalid argc_loc %s" % str(argc_loc))
            return

        if argv_loc is None:
            current_function = self.executor.bncache.get_function(
                self.executor.ip)
            argv_loc = current_function.calling_convention.int_arg_regs[1]

        if isinstance(argv_loc, str):
            setattr(state.regs, argv_loc, argv_p)
        elif isinstance(argv_loc, BV):
            state.mem.store(argv_loc, argv_p, state.arch.endness())
        else:
            log_alert("ERROR: invalid argv_loc %s" % str(argv_loc))
            return
