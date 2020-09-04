import traceback
import os
from binaryninja import (
    log_alert,
    log_info,
    BackgroundTaskThread,
    PluginCommand
)

from .sym_executor import SymbolicExecutor
from .utility.expr_wrap_util import split_bv_in_list
from .utility.bninja_util import get_address_after_merge
from .utility.string_util import (
    int_to_str,
    str_to_int,
    as_bytes,
    get_byte,
    str_to_bv_list
)
from .sym_state import State
from .models import function_models as seninja_models
from .expr import *
from .multipath import searcher
from .ui import (
    ui_set_arch, 
    ui_sync_view, 
    ui_reset_view, 
    enable_widgets, 
    disable_widgets
)
from . import settings

class TaskInBackground(BackgroundTaskThread):
    def __init__(self, bv, msg, callback):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bv = bv
        self.callback = callback
        self._i = 0

    def run(self):
        self.bv.update_analysis_and_wait()
        self.callback(self)

executor = None
dfs_searcher = None
searcher_tags = {}
_stop = False
_running = False

TARGET_TAG_TYPE = None
def get_target_tt(bv):
    global TARGET_TAG_TYPE
    if TARGET_TAG_TYPE is not None:
        return TARGET_TAG_TYPE
    TARGET_TAG_TYPE = bv.create_tag_type("searcher_target", "O")
    return TARGET_TAG_TYPE

AVOID_TAG_TYPE = None
def get_avoid_tt(bv):
    global AVOID_TAG_TYPE
    if AVOID_TAG_TYPE is not None:
        return AVOID_TAG_TYPE
    AVOID_TAG_TYPE = bv.create_tag_type("searcher_avoid", "X")
    return AVOID_TAG_TYPE

def __check_executor():
    if executor is None:
        log_alert("seninja not running")
        return False
    return True

def initialize_ui():
    if not __check_executor():
        return
    ui_set_arch(executor.arch, executor.state)

def sync_ui(bv, delta=True):
    if not __check_executor():
        return
    executor.set_colors()
    if executor.state is not None:
        ui_sync_view(executor.state, delta)
        bv.file.navigate(bv.file.view, executor.state.get_ip())
    else:
        disable_widgets()

def reset_ui():
    if not __check_executor():
        return
    ui_reset_view()

# --- async functions ---
def _async_start_se(bv, address):
    global _running
    if executor is not None:
        log_alert("seninja is already running")
        return False
    
    def f(tb):
        global executor, dfs_searcher, _running
        try:
            executor = SymbolicExecutor(bv, address)
        except Exception as e:
            print("!ERROR!")
            print(traceback.format_exc())
            _running = False
            return

        dfs_searcher = searcher.DFSSearcher(executor)
        initialize_ui()
        sync_ui(bv)
        enable_widgets()
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: starting symbolic execution", f)
        background_task.start()

def _set_run_target(bv, address):
    if not __check_executor():
        return

    address = get_address_after_merge(bv, address)
    func = executor.bncache.get_function(address)
    if address in searcher_tags:
        bv.remove_auto_data_tag(address, searcher_tags[address])
        del searcher_tags[address]

    tt = get_target_tt(bv)
    tag = func.create_auto_tag(tt, "SENINJA: target address")
    func.add_auto_address_tag(address, tag)
    searcher_tags[address] = tag
    if address == dfs_searcher.avoid:
        dfs_searcher.avoid.remove(address)

    dfs_searcher.set_target(address)

def _set_run_avoid(bv, address):
    if not __check_executor():
        return

    address = get_address_after_merge(bv, address)
    func = executor.bncache.get_function(address)
    if address in searcher_tags:
        bv.remove_auto_data_tag(address, searcher_tags[address])
        del searcher_tags[address]

    tt = get_avoid_tt(bv)
    tag = func.create_auto_tag(tt, "SENINJA: avoid address")
    func.add_auto_address_tag(address, tag)
    searcher_tags[address] = tag
    if address == dfs_searcher.target:
        dfs_searcher.target = None

    dfs_searcher.add_avoid(address)

def _async_run_dfs_searcher(bv):
    global _running
    if not __check_executor():
        return
    if not dfs_searcher.ready_to_run():
        log_alert("no target set for searcher")
        return
    
    def f(tb):
        global _running
        disable_widgets()

        def callback(s):
            global _stop
            tb.progress = "seninja: running DFS @ %s" % hex(s.get_ip())
            if _stop:
                _stop = False
                return False
            return True

        try:
            dfs_searcher.run(callback)
        except:
            print("!ERROR!")
            print(traceback.format_exc())

        sync_ui(bv, executor._last_error == None)
        enable_widgets()
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: running DFS", f)
        background_task.start()

def _async_step(bv):
    global _running
    if not __check_executor():
        return

    def f(tb):
        global _running
        disable_widgets()
        try:
            executor.execute_one()
        except Exception as e:
            print("!ERROR!")
            print(traceback.format_exc())

        sync_ui(bv, executor._last_error == None)
        enable_widgets()
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: stepping", f)
        background_task.start()

def _async_continue_until_branch(bv):
    global _running
    if not __check_executor():
        return

    def f(tb):
        global _running, _stop
        disable_widgets()

        k = len(executor.fringe.deferred)
        i = k
        count = 0
        while not _stop and i == k:
            try:
                executor.execute_one()
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            if not executor.state:
                break
            i = len(executor.fringe.deferred)
            ip = executor.state.get_ip()
            count = (count+1) % 20
            if count == 0:
                executor.set_colors()
            tb.progress = "seninja: continue until branch: %s" % hex(ip)

        sync_ui(bv, executor._last_error == None)
        enable_widgets()
        _running = False
        _stop = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until branch", f)
        background_task.start()

def _async_continue_until_address(bv, address):
    global _running
    if not __check_executor():
        return
    
    address = get_address_after_merge(bv, address)

    def f(tb):
        global _running, _stop
        disable_widgets()
        ip = executor.state.get_ip()

        count = 0
        while not _stop and ip != address:
            try:
                executor.execute_one()
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            if not executor.state:
                break
            ip = executor.state.get_ip()
            count = (count+1) % 20
            if count == 0:
                executor.set_colors()
            tb.progress = "seninja: continue until address: %s" % hex(ip)

        sync_ui(bv, executor._last_error == None)
        enable_widgets()
        _running = False
        _stop = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until address", f)
        background_task.start()

def _async_merge_states(bv, address):
    # merge all states at address and put them in current state. Current state must be at address
    global _running
    if not __check_executor():
        return

    if executor.state.get_ip() != address:
        log_alert("current state is not at this address")
        return

    to_be_merged = executor.fringe.get_all_deferred_by_address(address)
    if to_be_merged is None:
        log_alert("no deferred state at this address")
        return

    def f(tb):
        global _running
        disable_widgets()
        tot = len(to_be_merged)
        i = 0
        for s in to_be_merged:
            executor.state.merge(s)
            i += 1
            tb.progress = "seninja: merging states %d/%d" % (i, tot)
        
        sync_ui(bv)
        enable_widgets()
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: merging states", f)
        background_task.start()

def _async_change_current_state(bv, address):
    global _running
    if not __check_executor():
        return
    
    state = executor.fringe.get_deferred_by_address(address)
    if state is None:
        log_alert("no such deferred state")
        return
    
    def f(tb):
        global _running
        disable_widgets()

        executor.set_current_state(state)
        sync_ui(bv, delta=False)

        enable_widgets()
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: changing current state", f)
        background_task.start()

def _async_save_active_state(bv):
    global _running
    if not __check_executor():
        return
        
    def f(tb):
        global _running
        disable_widgets()

        saved_state = executor.state.copy()
        executor.put_in_deferred(saved_state)

        enable_widgets()
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: saving current state", f)
        background_task.start()

def _async_change_active_state_ip(bv, address):
    global _running
    if not __check_executor():
        return
        
    def f(tb):
        global _running
        disable_widgets()

        state = executor.state
        state.set_ip(address)
        func_name = executor.bncache.get_function_name(address)
        state.llil_ip = executor.bncache.get_llil_address(func_name, address)

        executor.state = None
        executor.set_current_state(state)

        sync_ui(bv, delta=False)

        enable_widgets()
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: changing current state", f)
        background_task.start()

def _async_reset_se(bv):
    global _running
    if not __check_executor():
        return
    
    def f(tb):
        global _running, executor

        for addr in searcher_tags:
            tag = searcher_tags[addr]
            func = executor.bncache.get_function(addr)
            func.remove_auto_address_tag(addr, tag)

        disable_widgets()
        executor.reset()
        reset_ui()
        executor = None
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: resetting symbolic execution", f)
        background_task.start()
# --- end async functions ---

# APIs (other file?)

def start_se(bv, address, sync=False):
    global executor
    if executor is not None:
        log_alert("seninja is already running")
        return False
    executor = SymbolicExecutor(bv, address)
    if sync:
        sync_ui(bv)

def continue_until_branch(sync=False):
    global _stop
    if not __check_executor():
        return

    k = executor.fringe.last_added
    i = k
    while not _stop and i == k:
        try:
            executor.execute_one()
        except Exception as e:
            print("!ERROR!:")
            print(traceback.format_exc())
            break
        if not executor.state:
            break
        i = executor.fringe.last_added

    _stop = False
    if sync:
        sync_ui(executor.state.bv)
    return executor.state, executor.fringe.last_added

def continue_until_address(address, sync=False):
    ip = executor.state.get_ip()

    while ip != address:
        try:
            executor.execute_one()
        except Exception as e:
            print("!ERROR!:")
            print(traceback.format_exc())
            break
        if not executor.state:
            break
        ip = executor.state.get_ip()

    if sync:
        sync_ui(executor.state.bv)
    return executor.state

def run_dfs(target: int, avoid:list=None, sync=False):
    global _stop
    if not __check_executor():
        return

    def callback(s):
        if _stop:
            _stop = False
            return False
        return True

    dfs_s = searcher.DFSSearcher(executor)
    dfs_s.set_target(target)
    if avoid is not None:
        for a in avoid:
            dfs_s.add_avoid(a)

    res = dfs_s.run(callback)
    if sync:
        sync_ui(executor.state.bv)
    return res

def execute_one_instruction(bv, sync=None):
    if not __check_executor():
        return

    try:
        executor.execute_one()
    except Exception as e:
        print("!ERROR!:")
        print(traceback.format_exc())
        return

    if sync:
        sync_ui(bv)
    return executor.state

def change_current_state(address_or_state, sync=False):
    # take only the first one at the given address. TODO
    if not __check_executor():
        return

    if not isinstance(address_or_state, State):
        state = executor.fringe.get_deferred_by_address(address_or_state)
    else:
        state = address_or_state
    if state is None:
        log_alert("no such deferred state")
        return

    if sync:
        sync_ui(state.bv)
    executor.set_current_state(state)

def focus_current_state(bv):
    if not __check_executor():
        return
    bv.file.navigate(bv.file.view, executor.state.get_ip())

def reset_se(bv=None):
    global executor
    if not __check_executor():
        return

    executor.reset()
    reset_ui()
    executor = None

def stop():
    global _stop
    if _running:  # race conditions?
        _stop = True

def get_current_state():
    if not __check_executor():
        return

    return executor.state

def register_hook(address, func):
    if not __check_executor():
        return

    executor.user_hooks[address] = func

def register_logger(address, func):
    if not __check_executor():
        return

    executor.user_loggers[address] = func

def reload_settings():
    if not __check_executor():
        return

    executor.bncache.settings = {}

PluginCommand.register_for_address(
    "SENinja\\0 - Start symbolic execution",
    "create the first state for symbolic execution at current address",
    _async_start_se
)
PluginCommand.register_for_address(
    "SENinja\\1 - Change current state",
    "change current state with the deferred one at current address (if any)",
    _async_change_current_state
)
PluginCommand.register(
    "SENinja\\2 - Step",
    "execute one instruction with the current state",
    _async_step
)
PluginCommand.register(
    "SENinja\\3 - Continue until branch",
    "execute instructions in the current state until a fork occurs",
    _async_continue_until_branch
)
PluginCommand.register_for_address(
    "SENinja\\4 - Continue until address",
    "execute instructions in the current state until the currently selected address is reached",
    _async_continue_until_address
)
PluginCommand.register_for_address(
    "SENinja\\5 - Merge states",
    "merge all states at current address in one state",
    _async_merge_states
)
PluginCommand.register(
    "SENinja\\6 - Save active state",
    "save active state in deferred queue",
    _async_save_active_state
)
PluginCommand.register_for_address(
    "SENinja\\7 - Set IP to address",
    "set ip of active state to current address",
    _async_change_active_state_ip
)
PluginCommand.register_for_address(
    "SENinja\\8 - Run\\0 - Set target",
    "set run target",
    _set_run_target
)
PluginCommand.register_for_address(
    "SENinja\\8 - Run\\1 - Set avoid",
    "set run avoid",
    _set_run_avoid
)
PluginCommand.register(
    "SENinja\\8 - Run\\2 - Run (DFS)",
    "run (target must be set)",
    _async_run_dfs_searcher
)
PluginCommand.register(
    "SENinja\\9 - Reset symbolic execution",
    "delete all states",
    _async_reset_se
)
