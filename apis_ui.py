from .seninja_globals import globs
from .ui import (
    ui_sync_view,
    ui_reset_view,
    enable_widgets,
    disable_widgets,
    ui_set_arch
)
from binaryninja import (
    log_alert,
    log_info,
    BackgroundTaskThread,
    PluginCommand,
    enums
)
from binaryninja.interaction import get_choice_input
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
from .utility.exceptions import SENinjaError

import time
import sys

NO_COLOR = enums.HighlightStandardColor(0)
HIGHLIGHTED_HISTORY_COLOR = enums.HighlightStandardColor.YellowHighlightColor


# TODO bring all logic from here to apis.py

class TaskInBackground(BackgroundTaskThread):
    def __init__(self, bv, msg, callback):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bv = bv
        self.callback = callback
        self._i = 0

    def run(self):
        self.bv.update_analysis_and_wait()
        self.callback(self)


def __check_executor():
    if globs.executor is None:
        log_alert("seninja not running")
        return False
    return True


def ui_reset_state_history_highlight():
    if len(globs.highlighted_state_history) > 0:
        # Remove highlight
        for insn in globs.highlighted_state_history:
            func = globs.executor.bncache.get_function(insn)
            func.set_auto_instr_highlight(insn, NO_COLOR)

        globs.highlighted_state_history = list()


def sync_ui(bv, delta=True):
    if not __check_executor():
        return

    ui_reset_state_history_highlight()

    globs.executor.set_colors()
    if globs.executor.state is not None:
        ui_sync_view(globs.executor.state, delta)
        bv.file.navigate(bv.file.view, globs.executor.state.get_ip())
    else:
        disable_widgets()


def reset_ui():
    if not __check_executor():
        return
    ui_reset_state_history_highlight()
    ui_reset_view()


def get_target_tt(bv):
    if globs.TARGET_TAG_TYPE is not None:
        return globs.TARGET_TAG_TYPE
    globs.TARGET_TAG_TYPE = "searcher_target"
    bv.create_tag_type(globs.TARGET_TAG_TYPE, "O")
    return globs.TARGET_TAG_TYPE


def get_avoid_tt(bv):
    if globs.AVOID_TAG_TYPE is not None:
        return globs.AVOID_TAG_TYPE
    globs.AVOID_TAG_TYPE = "searcher_avoid"
    bv.create_tag_type(globs.AVOID_TAG_TYPE, "X")
    return globs.AVOID_TAG_TYPE


def initialize_ui():
    if not __check_executor():
        return
    ui_set_arch(globs.executor.arch, globs.executor.state)


def _async_start_se(bv, address):
    globs.started_address = address
    if globs.executor is not None:
        log_alert("seninja is already running")
        return False

    def f(tb):
        try:
            globs.executor = SymbolicExecutor(bv, address)
        except SENinjaError as e:
            sys.stderr.write(e.message + "\n")
            globs._running = False
            return

        globs.dfs_searcher = searcher.DFSSearcher(globs.executor)
        globs.bfs_searcher = searcher.BFSSearcher(globs.executor)
        globs._running = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(
            bv, "seninja: starting symbolic execution", f)
        background_task.start()
        background_task.join()

        if not __check_executor():
            # something wrong
            return

        globs.bv = bv
        globs.actions_step = _async_step
        globs.actions_dfs = _async_run_dfs_searcher
        globs.actions_bfs = _async_run_bfs_searcher
        globs.actions_reset = _async_reset_se
        globs.actions_change_state = _async_change_current_state
        initialize_ui()
        sync_ui(bv)
        enable_widgets()


def _async_toggle_state_history(bv):
    if not __check_executor():
        return

    if globs.executor.state is None:
        return

    if globs.executor.bncache.get_setting("save_state_history") == "false":
        log_alert("State history is not saved. This can be changed in settings")
        return

    if len(globs.highlighted_state_history) > 0:
        # Remove highlight
        ui_reset_state_history_highlight()

    else:
        # Set highlight
        for insn in globs.executor.state.insn_history:
            globs.highlighted_state_history.append(insn)
            func = globs.executor.bncache.get_function(insn)
            func.set_auto_instr_highlight(insn, HIGHLIGHTED_HISTORY_COLOR)


def _set_run_target(bv, address):
    if not __check_executor():
        return

    address = get_address_after_merge(bv, address)
    func = globs.executor.bncache.get_function(address)
    if address in globs.searcher_tags:
        func.remove_auto_address_tags_of_type(address, globs.searcher_tags[address])
        del globs.searcher_tags[address]

    tt = get_target_tt(bv)
    func.add_tag(tt, "SENINJA: target address", address, True)
    globs.searcher_tags[address] = tt
    if address in globs.dfs_searcher.avoid:
        globs.dfs_searcher.avoid.remove(address)
        globs.bfs_searcher.avoid.remove(address)

    globs.dfs_searcher.set_target(address)
    globs.bfs_searcher.set_target(address)


def _set_run_avoid(bv, address):
    if not __check_executor():
        return

    address = get_address_after_merge(bv, address)
    func = globs.executor.bncache.get_function(address)
    if address in globs.searcher_tags:
        func.remove_auto_address_tags_of_type(address, globs.searcher_tags[address])
        del globs.searcher_tags[address]

    tt = get_avoid_tt(bv)
    func.add_tag(tt, "SENINJA: avoid address", address, True)
    globs.searcher_tags[address] = tt
    if address == globs.dfs_searcher.target:
        globs.dfs_searcher.target = None
        globs.bfs_searcher.target = None

    globs.dfs_searcher.add_avoid(address)
    globs.bfs_searcher.add_avoid(address)


def _async_run_dfs_searcher(bv):
    if not __check_executor():
        return
    if not globs.dfs_searcher.ready_to_run():
        log_alert("no target set for searcher")
        return

    timeout = globs.executor.bncache.get_setting("exploration_timeout")
    timeout = int(timeout)

    def f(tb):
        start = time.time()
        def callback(s):
            if s is None:
                return False
            tb.progress = "seninja: running DFS @ %s" % hex(s.get_ip())
            if timeout > 0 and time.time() - start > timeout:
                # Timeout elapsed
                print("[!] Timeout elapsed (%d sec)" % timeout)
                return False
            if globs._stop:
                globs._stop = False
                return False
            return True

        globs.dfs_searcher.run(step_callback=callback)

        enable_widgets()
        sync_ui(bv, globs.executor._last_error == None)
        globs._running = False

    if not globs._running:
        globs._running = True
        disable_widgets()
        background_task = TaskInBackground(bv, "seninja: running DFS", f)
        background_task.start()


def _async_run_dfs_searcher_findall(bv):
    if not __check_executor():
        return
    if not globs.dfs_searcher.ready_to_run():
        log_alert("no target set for searcher")
        return

    timeout = globs.executor.bncache.get_setting("exploration_timeout")
    timeout = int(timeout)

    def f(tb):
        start = time.time()
        def callback(s):
            if s is None:
                return False
            tb.progress = "seninja: running DFS @ %s" % hex(s.get_ip())
            if timeout > 0 and time.time() - start > timeout:
                # Timeout elapsed
                print("[!] Timeout elapsed (%d sec)" % timeout)
                return False
            if globs._stop:
                globs._stop = False
                return False
            return True

        globs.dfs_searcher.run(step_callback=callback, findall=True)

        enable_widgets()
        sync_ui(bv, globs.executor._last_error == None)
        globs._running = False

    if not globs._running:
        disable_widgets()
        globs._running = True
        background_task = TaskInBackground(bv, "seninja: running DFS", f)
        background_task.start()


def _async_run_bfs_searcher(bv):
    if not __check_executor():
        return

    if not globs.bfs_searcher.ready_to_run():
        log_alert("no target set for searcher")
        return

    timeout = globs.executor.bncache.get_setting("exploration_timeout")
    timeout = int(timeout)

    def f(tb):
        start = time.time()
        def callback(s):
            if s is None:
                return False
            tb.progress = "seninja: running BFS @ %s" % hex(s.get_ip())
            if timeout > 0 and time.time() - start > timeout:
                # Timeout elapsed
                print("[!] Timeout elapsed (%d sec)" % timeout)
                return False
            if globs._stop:
                globs._stop = False
                return False
            return True

        globs.bfs_searcher.run(callback)

        enable_widgets()
        sync_ui(bv, globs.executor._last_error == None)
        globs._running = False

    if not globs._running:
        disable_widgets()
        globs._running = True
        background_task = TaskInBackground(bv, "seninja: running BFS", f)
        background_task.start()


def _async_step(bv):
    if not __check_executor():
        return

    def f(tb):
        disable_widgets()

        globs.executor.execute_one()

        sync_ui(bv, globs.executor._last_error == None)
        enable_widgets()
        globs._running = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(bv, "seninja: stepping", f)
        background_task.start()


def _async_continue_until_branch(bv):
    if not __check_executor():
        return

    timeout = globs.executor.bncache.get_setting("exploration_timeout")
    timeout = int(timeout)

    def f(tb):
        disable_widgets()

        start = time.time()
        k = len(globs.executor.fringe.deferred)
        i = k
        count = 0
        while not globs._stop and i == k:
            globs.executor.execute_one()
            if not globs.executor.state:
                break

            if timeout > 0 and time.time() - start > timeout:
                # Timeout elapsed
                print("[!] Timeout elapsed (%d sec)" % timeout)
                break

            i = len(globs.executor.fringe.deferred)
            ip = globs.executor.state.get_ip()
            count = (count+1) % 20
            if count == 0:
                globs.executor.set_colors()
            tb.progress = "seninja: continue until branch: %s" % hex(ip)

        sync_ui(bv, globs.executor._last_error == None)
        enable_widgets()
        globs._running = False
        globs._stop = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(
            bv, "seninja: continue until branch", f)
        background_task.start()


def _async_continue_until_address(bv, address):
    if not __check_executor():
        return

    timeout = globs.executor.bncache.get_setting("exploration_timeout")
    timeout = int(timeout)

    address = get_address_after_merge(bv, address)

    def f(tb):
        disable_widgets()
        ip = globs.executor.state.get_ip()
        start = time.time()

        count = 0
        while not globs._stop and ip != address:
            globs.executor.execute_one()
            if not globs.executor.state:
                break

            if timeout > 0 and time.time() - start > timeout:
                # Timeout elapsed
                print("[!] Timeout elapsed (%d sec)" % timeout)
                break

            ip = globs.executor.state.get_ip()
            count = (count+1) % 20
            if count == 0:
                globs.executor.set_colors()
            tb.progress = "seninja: continue until address: %s" % hex(ip)

        sync_ui(bv, globs.executor._last_error == None)
        enable_widgets()
        globs._running = False
        globs._stop = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(
            bv, "seninja: continue until address", f)
        background_task.start()


def _async_merge_states(bv, address):
    # merge all states at address and put them in current state. Current state must be at address
    if not __check_executor():
        return

    if globs.executor.state.get_ip() != address:
        log_alert("current state is not at this address")
        return

    to_be_merged_all = globs.executor.fringe.get_all_deferred_by_address(
        address)
    if to_be_merged_all is None:
        log_alert("no deferred state at this address")
        return

    mergeable, not_mergeable = globs.executor.extract_mergeable_with_current_state(
        to_be_merged_all)
    if len(not_mergeable) > 0:
        print(
            "WARNING: %d states was not merged since they deviate from the current state after executing the current instruction" % len(not_mergeable))
        globs.executor.fringe._deferred[address] = not_mergeable

    if len(mergeable) == 0:
        return
    to_be_merged = mergeable

    def f(tb):
        disable_widgets()
        tot = len(to_be_merged)
        i = 0
        for s in to_be_merged:
            globs.executor.state.merge(s)
            i += 1
            tb.progress = "seninja: merging states %d/%d" % (i, tot)

        globs.executor.delete_comment_for_address(address)
        sync_ui(bv)
        enable_widgets()
        globs._running = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(bv, "seninja: merging states", f)
        background_task.start()


def _async_change_current_state(bv, address):
    if not __check_executor():
        return

    states = globs.executor.fringe.get_list_deferred_by_address(address)
    if len(states) == 0:
        log_alert("no such deferred state")
        return
    if len(states) == 1:
        state = globs.executor.fringe.get_deferred_by_address(address)
    else:
        state_idx = get_choice_input(
            "Select state", "states", list(map(str, states)))
        state = globs.executor.fringe.get_deferred_by_address(
            address, state_idx)

    disable_widgets()
    globs.executor.delete_comment_for_address(address)
    globs.executor.set_current_state(state)
    sync_ui(bv, delta=False)
    enable_widgets()


def _async_save_active_state(bv):
    if not __check_executor():
        return

    def f(tb):
        disable_widgets()

        saved_state = globs.executor.state.copy()
        globs.executor.put_in_deferred(saved_state)

        enable_widgets()
        globs._running = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(
            bv, "seninja: saving current state", f)
        background_task.start()


def _async_change_active_state_ip(bv, address):
    if not __check_executor():
        return

    def f(tb):
        disable_widgets()

        state = globs.executor.state
        state.set_ip(address)
        func_name = globs.executor.bncache.get_function_name(address)
        state.llil_ip = globs.executor.bncache.get_llil_address(
            func_name, address)

        globs.executor.state = None
        globs.executor.set_current_state(state)

        sync_ui(bv, delta=False)

        enable_widgets()
        globs._running = False

    if not globs._running:
        globs._running = True
        background_task = TaskInBackground(
            bv, "seninja: changing current state", f)
        background_task.start()


def _async_reset_se(bv, address):
    if not __check_executor():
        return

    def f(tb):
        for addr in globs.searcher_tags:
            tag = globs.searcher_tags[addr]
            func = globs.executor.bncache.get_function(addr)
            func.remove_auto_address_tags_of_type(addr, tag)
        globs.searcher_tags = dict()

        globs.executor.reset()
        globs.executor = None
        globs._running = False

    if not globs._running:
        globs._running = True

        disable_widgets()
        reset_ui()
        # just an hack to redraw widgets. find another way
        bv.file.navigate(bv.file.view, address)

        background_task = TaskInBackground(
            bv, "seninja: resetting symbolic execution", f)
        background_task.start()
