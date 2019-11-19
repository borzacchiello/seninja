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
from utility.z3_wrap_util import bvv, bvs
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
    global sv
    if sv is None:
        log_alert("seninja not running")
        return False
    return True

def start_se(bv, address):
    global sv, _running
    if sv is not None:
        log_alert("seninja is already running")
        return False
    
    def f(tb):
        global sv, _running
        sv = SymbolicVisitor(bv, address)
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: starting symbolic execution", f)
        background_task.start()

def reset_se():
    global sv
    if not __check_sv():
        return
    
    sv._set_colors(reset=True)
    sv = None

def step(bv):
    global sv, _running
    if not __check_sv():
        return
    
    def f(tb):
        global sv, _running
        try:
            sv.execute_one()
        except Exception as e:
            print("!ERROR!")
            print(traceback.format_exc())
        _running = False

    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: stepping", f)
        background_task.start()

def continue_until_branch(bv):
    global sv, _running
    if not __check_sv():
        return
    
    def f(tb):
        global sv, _running, _stop

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
            i = len(sv.fringe.deferred)
            ip = sv.state.get_ip()
            count = (count+1) % 20
            tb.progress = "seninja: continue until branch: %s" % hex(ip)
        sv._set_colors()
        _running = False
        _stop = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until branch", f)
        background_task.start()

def continue_until_address(bv, address):
    global sv, _running
    if not __check_sv():
        return
    
    def f(tb):
        global sv, _running, _stop
        ip = sv.state.get_ip()

        count = 0
        while not _stop and ip != address:
            try:
                sv.execute_one(no_colors=(count != 0))
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            ip = sv.state.get_ip()
            count = (count+1) % 20
            tb.progress = "seninja: continue until address: %s" % hex(ip)
        sv._set_colors()
        _running = False
        _stop = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: continue until address", f)
        background_task.start()

def change_current_state(bv, address):
    # take only the first one at the given address. TODO
    global sv
    if not __check_sv():
        return

    state = sv.fringe.get_deferred_by_address(address)
    if state is None:
        log_alert("no such deferred state")
        return
    
    sv.set_current_state(state)

def merge_states(bv, address):
    # merge all states at address and put them in current state. Current state must be at address
    global sv, _running
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
        global sv, _running
        tot = len(to_be_merged)
        i = 0
        for s in to_be_merged:
            sv.state.merge(s)
            i += 1
            tb.progress = "seninja: merging states: %d/%d" % (i, tot)
        _running = False
    
    if not _running:
        _running = True
        background_task = TaskInBackground(bv, "seninja: merging states", f)
        background_task.start()

def stop():
    global _running, _stop
    if _running:  # race conditions?
        _stop = True

def get_current_state():
    global sv
    if not __check_sv():
        return
    
    return sv.state

PluginCommand.register_for_address("seninja: start symbolic execution", "", start_se)
PluginCommand.register_for_address("seninja: change current state", "", change_current_state)
PluginCommand.register("seninja: step", "", step)
PluginCommand.register("seninja: continue until branch", "", continue_until_branch)
PluginCommand.register_for_address("seninja: continue until address", "", continue_until_address)
PluginCommand.register_for_address("seninja: merge states", "", merge_states)
