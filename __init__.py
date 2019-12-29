import traceback
import sys
import os
path = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, path)

from sym_executor import *
from binaryninja import (
    log_alert, 
    log_info,
    BackgroundTaskThread,
    PluginCommand
)
from utility.expr_wrap_util import split_bv_in_list
from utility.string_util import (
    int_to_str, 
    str_to_int, 
    as_bytes,
    get_byte
)
import options as seninja_opts
import models.function_models as seninja_models
from expr import *

class TaskInBackground(BackgroundTaskThread):
    def __init__(self, bv, msg, callback):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bv = bv
        self.callback = callback
        self._i = 0

    def run(self):
        self.bv.update_analysis_and_wait()
        self.callback(self)

sv = None
_stop = False
_running = False

def __check_sv():
    if sv is None:
        log_alert("seninja not running")
        return False
    return True

# --- async functions ---
def _async_start_se(bv, address):
    global _running
    if sv is not None:
        log_alert("seninja is already running")
        return False
    
    def f(tb):
        global sv, _running
        sv = SymbolicVisitor(bv, address)
        bv.file.navigate(bv.file.view, sv.state.get_ip())
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: starting symbolic execution", f)
        background_task.start()

def _async_step(bv):
    global _running
    if not __check_sv():
        return
    
    def f(tb):
        global _running
        try:
            sv.execute_one()
        except Exception as e:
            print("!ERROR!")
            print(traceback.format_exc())
        
        bv.file.navigate(bv.file.view, sv.state.get_ip())
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: stepping", f)
        background_task.start()

def _async_continue_until_branch(bv):
    global _running
    if not __check_sv():
        return
    
    def f(tb):
        global _running, _stop

        k = len(sv.fringe.deferred)
        i = k
        count = 0
        while not _stop and i == k:
            try:
                sv.execute_one(no_colors=(count != 0))
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            if not sv.state:
                break
            i = len(sv.fringe.deferred)
            ip = sv.state.get_ip()
            count = (count+1) % 20
            tb.progress = "seninja: continue until branch: %s" % hex(ip)
        
        bv.file.navigate(bv.file.view, sv.state.get_ip())
        sv._set_colors()
        _running = False
        _stop = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until branch", f)
        background_task.start()

def _async_continue_until_address(bv, address):
    global _running
    if not __check_sv():
        return
    
    def f(tb):
        global _running, _stop
        ip = sv.state.get_ip()

        count = 0
        while not _stop and ip != address:
            try:
                sv.execute_one(no_colors=(count != 0))
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            if not sv.state:
                break
            ip = sv.state.get_ip()
            count = (count+1) % 20
            tb.progress = "seninja: continue until address: %s" % hex(ip)
        
        bv.file.navigate(bv.file.view, sv.state.get_ip())
        sv._set_colors()
        _running = False
        _stop = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until address", f)
        background_task.start()

def _async_merge_states(bv, address):
    # merge all states at address and put them in current state. Current state must be at address
    global _running
    if not __check_sv():
        return

    if sv.state.get_ip() != address:
        log_alert("current state is not at this address")
        return

    to_be_merged = sv.fringe.get_all_deferred_by_address(address)
    if to_be_merged is None:
        log_alert("no deferred state at this address")
        return
    
    def f(tb):
        global _running
        tot = len(to_be_merged)
        i = 0
        for s in to_be_merged:
            sv.state.merge(s)
            i += 1
            tb.progress = "seninja: merging states %d/%d" % (i, tot)
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: merging states", f)
        background_task.start()
# --- end async functions ---

def start_se(bv, address):
    global sv
    if sv is not None:
        log_alert("seninja is already running")
        return False
    sv = SymbolicVisitor(bv, address)
    bv.file.navigate(bv.file.view, sv.state.get_ip())

def continue_until_branch():
    global _stop
    if not __check_sv():
        return

    k = len(sv.fringe.deferred)
    i = k
    while not _stop and i == k:
        try:
            sv.execute_one(no_colors=True)
        except Exception as e:
            print("!ERROR!:")
            print(traceback.format_exc())
            break
        if not sv.state:
            break
        i = len(sv.fringe.deferred)

    sv.view.file.navigate(sv.view.file.view, sv.state.get_ip())
    sv._set_colors()
    _running = False
    _stop = False

    return sv.state, sv.fringe.last_added

def change_current_state(bv, address):
    # take only the first one at the given address. TODO
    if not __check_sv():
        return

    state = sv.fringe.get_deferred_by_address(address)
    if state is None:
        log_alert("no such deferred state")
        return
    
    sv.set_current_state(state)
    bv.file.navigate(bv.file.view, sv.state.get_ip())

def reset_se(bv):
    global sv
    if not __check_sv():
        return
    
    sv._reset()
    sv = None

def stop():
    global _stop
    if _running:  # race conditions?
        _stop = True

def get_current_state():
    if not __check_sv():
        return
    
    return sv.state

def register_hook(address, func):
    if not __check_sv():
        return

    sv.user_hooks[address] = func

PluginCommand.register_for_address(
    "SENinja\\0 - Start symbolic execution", 
    "create the first state for symbolic execution at current address", 
    _async_start_se
)
PluginCommand.register_for_address(
    "SENinja\\1 - Change current state", 
    "change current state with the deferred one at current address (if any)", 
    change_current_state
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
    "SENinja\\6 - Reset symbolic execution", 
    "delete all states", 
    reset_se
)
