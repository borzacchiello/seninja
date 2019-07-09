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

class TaskInBackground(BackgroundTaskThread):
    def __init__(self, bv, msg, callback):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bv = bv
        self.callback = callback
        self._i = 0

    def run(self):
        self.bv.update_analysis_and_wait()
        self.callback()

sv = None
running = False

def __check_sv():
    global sv
    if sv is None:
        log_alert("seninja not running")
        return False
    return True

def start_se(bv, address):
    global sv
    if sv is not None:
        log_alert("seninja is already running")
        return False
    sv = SymbolicVisitor(bv, address)

def reset_se():
    global sv
    if not __check_sv():
        return
    
    sv._set_colors(reset=True)
    sv = None

def step(bv):
    global sv, running
    if not __check_sv():
        return
    
    def f():
        global sv, running
        sv.execute_one()
        running = False

    if not running:
        running = True
        background_task = TaskInBackground(bv, "seninja: stepping", f)
        background_task.start()

def continue_until_branch(bv):
    global sv, running
    if not __check_sv():
        return
    
    def f():
        global sv, running

        k = len(sv.fringe.deferred)
        i = k
        while i == k:
            sv.execute_one()
            i = len(sv.fringe.deferred)
        running = False
    
    if not running:
        running = True
        background_task = TaskInBackground(bv, "seninja: continue until branch", f)
        background_task.start()

def continue_until_address(bv, address):
    global sv, running
    if not __check_sv():
        return
    
    def f():
        global sv, running
        while sv.state.get_ip() != address:
            sv.execute_one()
        running = False
    
    if not running:
        running = True
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

def get_current_state():
    global sv
    if not __check_sv():
        return
    
    return sv.state

PluginCommand.register("seninja: step", "", step)
PluginCommand.register("seninja: continue until branch", "", continue_until_branch)
PluginCommand.register_for_address("seninja: continue until address", "", continue_until_address)
PluginCommand.register_for_address("seninja: start symbolic execution", "", start_se)
PluginCommand.register_for_address("seninja: change current state", "", change_current_state)
