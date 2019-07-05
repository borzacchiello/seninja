import sys
import os
path = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, path)

from sym_executor import *
from binaryninja import log_alert, PluginCommand
from utility.z3_wrap_util import bvv, bvs

sv = None

def __check_sv():
    global sv
    if sv is None:
        log_alert("seninja not running")
        return False
    return True

def start_se(bv, address):
    global sv
    sv = SymbolicVisitor(bv, address)

def step(bv):
    global sv
    if not __check_sv():
        return

    sv.execute_one()

def continue_until_branch(bv):
    global sv
    if not __check_sv():
        return
    
    k = len(sv.fringe.deferred)
    i = k
    while i == k:
        sv.execute_one()
        i = len(sv.fringe.deferred)

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
PluginCommand.register_for_address("seninja: start symbolic execution", "", start_se)
PluginCommand.register_for_address("seninja: change current state", "", change_current_state)
