import threading
import time
import sys

from binaryninja.interaction import get_choice_input
from binaryninja import (
    enums,
    log_alert,
    BackgroundTaskThread,
)
from binaryninjaui import UIContext

from .seninja_widget import SENinjaWidgetType
from .argv_form import GetArgvDialog
from ..utility.bninja_util import get_address_after_merge
from ..utility.exceptions import SENinjaError
from ..sym_executor import SymbolicExecutor
from ..multipath import searcher

class UIBackgroundTask(BackgroundTaskThread):
    def __init__(self, bv, msg, callback):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bv       = bv
        self.callback = callback
        self._i       = 0

    def run(self):
        self.bv.update_analysis_and_wait()
        self.callback(self)

class UIManager(object):
    TARGET_TAG_TYPE = None
    AVOID_TAG_TYPE = None

    NO_COLOR = enums.HighlightStandardColor(0)
    CURR_STATE_COLOR = enums.HighlightStandardColor.GreenHighlightColor
    DEFERRED_STATE_COLOR = enums.HighlightStandardColor.RedHighlightColor
    ERRORED_STATE_COLOR = enums.HighlightStandardColor.BlackHighlightColor
    HIGHLIGHTED_HISTORY_COLOR = enums.HighlightStandardColor.YellowHighlightColor

    @staticmethod
    def get_target_tt(bv):
        if UIManager.TARGET_TAG_TYPE is not None:
            return UIManager.TARGET_TAG_TYPE
        UIManager.TARGET_TAG_TYPE = "SENinja Target"
        bv.create_tag_type(UIManager.TARGET_TAG_TYPE, "O")
        return UIManager.TARGET_TAG_TYPE

    @staticmethod
    def get_avoid_tt(bv):
        if UIManager.AVOID_TAG_TYPE is not None:
            return UIManager.AVOID_TAG_TYPE
        UIManager.AVOID_TAG_TYPE = "SENinja Avoid"
        bv.create_tag_type(UIManager.AVOID_TAG_TYPE, "X")
        return UIManager.AVOID_TAG_TYPE

    @property
    def bv(self):
        ctx = UIContext.activeContext()
        if ctx is None:
            return None
        view = ctx.getCurrentView()
        if view is None:
            return None
        return view.getData()

    @property
    def widget(self):
        if self._widget is not None:
            return self._widget
        ctx = UIContext.activeContext()
        if ctx is None:
            return None
        view_frame = ctx.getCurrentViewFrame()
        if view_frame is None:
            return None
        sidebar = view_frame.getSidebar()
        if sidebar is None:
            return None
        self._widget = sidebar.widget(SENinjaWidgetType.name)
        return self._widget

    # decorator
    def locked(func):
        def wrapper(self, *args, **kwargs):
            with self.lock:
                r = func(self, *args, **kwargs)
            return r
        return wrapper

    def __init__(self):
        self.lock    = threading.RLock()
        self._widget = None

        self.executor      = None
        self.dfs_searcher  = None
        self.bfs_searcher  = None
        self.searcher_tags = {}
        self.running       = False
        self.stop          = False

        self.highlighted_state_history = list()

    def symbolic_started(self):
        if self.executor is not None:
            return True
        log_alert("SENinja not running")
        return False

    def reset_state_history_highlight(self):
        if len(self.highlighted_state_history) > 0:
            # Remove highlight
            for insn in self.highlighted_state_history:
                func = self.executor.bncache.get_function(insn)
                func.set_auto_instr_highlight(insn, UIManager.NO_COLOR)
            self.highlighted_state_history = list()

    def _initialize_ui(self):
        if not self.symbolic_started():
            return
        self.widget.initSignal.emit(self.executor.arch, self.executor.state)

    def _sync_ui(self, delta=True):
        if not self.symbolic_started():
            return

        self.reset_state_history_highlight()
        self._set_colors()
        if self.executor.state is not None:
            self.widget.updateStateSignal.emit(self.executor.state)
            self.bv.file.navigate(self.bv.file.view, self.executor.state.get_ip())

    def _reset_ui(self):
        if not self.symbolic_started():
            return

        self.reset_state_history_highlight()
        self.widget.resetSignal.emit()

    def _delete_comment_for_address(self, address):
        if not self.symbolic_started():
            return

        func = self.executor.bncache.get_function(address)
        func.set_comment_at(address, None)

    def _set_colors(self, reset=False):
        if not self.symbolic_started():
            return

        old_ip = self.executor._last_colored_ip
        if old_ip is not None:
            old_func = self.executor.bncache.get_function(old_ip)
            old_func.set_auto_instr_highlight(old_ip, UIManager.NO_COLOR)

        for ip in self.executor.fringe._deferred:
            func = self.executor.bncache.get_function(ip)
            func.set_auto_instr_highlight(
                ip, UIManager.DEFERRED_STATE_COLOR if not reset else UIManager.NO_COLOR)
            if reset:
                func.set_comment_at(ip, None)
            elif len(self.executor.fringe._deferred[ip]) > 1 or (len(self.executor.fringe._deferred[ip]) == 1 and self.executor.ip == ip):
                func.set_comment_at(ip, "n deferred: %d" %
                                    len(self.executor.fringe._deferred[ip]))

        for _, state in self.executor.fringe.errored:
            func = self.executor.bncache.get_function(state.get_ip())
            func.set_auto_instr_highlight(
                state.get_ip(), UIManager.ERRORED_STATE_COLOR if not reset else UIManager.NO_COLOR)

        if self.executor.state:
            func = self.executor.bncache.get_function(self.executor.ip)
            func.set_auto_instr_highlight(
                self.executor.ip, UIManager.CURR_STATE_COLOR if not reset else UIManager.NO_COLOR)
        if not reset:
            self.executor._last_colored_ip = self.executor.ip

    @locked
    def start_se(self):
        if self.executor is not None:
            log_alert("SENinja already started")
            return

        address = self.bv.file.offset
        try:
            self.executor = SymbolicExecutor(self.bv, address)
        except SENinjaError as e:
            sys.stderr.write(e.message + "\n")
            return
        self.dfs_searcher = searcher.DFSSearcher(self.executor)
        self.bfs_searcher = searcher.BFSSearcher(self.executor)

        self._initialize_ui()
        self._sync_ui()

    @locked
    def set_run_target(self, address):
        if not self.symbolic_started():
            return

        address = get_address_after_merge(self.bv, address)
        func = self.executor.bncache.get_function(address)
        if address in self.searcher_tags:
            func.remove_auto_address_tags_of_type(address, self.searcher_tags[address][0])
            del self.searcher_tags[address]

        tt = UIManager.get_target_tt(self.bv)
        func.add_tag(tt, "SENINJA: target address", address, True)
        self.searcher_tags[address] = (tt, func)
        if address in self.dfs_searcher.avoid:
            self.dfs_searcher.avoid.remove(address)
            self.bfs_searcher.avoid.remove(address)

        self.dfs_searcher.set_target(address)
        self.bfs_searcher.set_target(address)

    @locked
    def set_run_avoid(self, address):
        if not self.symbolic_started():
            return

        address = get_address_after_merge(self.bv, address)
        func = self.executor.bncache.get_function(address)
        if address in self.searcher_tags:
            func.remove_auto_address_tags_of_type(address, self.searcher_tags[address])
            del self.searcher_tags[address]

        tt = UIManager.get_avoid_tt(self.bv)
        func.add_tag(tt, "SENINJA: avoid address", address, True)
        self.searcher_tags[address] = (tt, func)
        if address == self.dfs_searcher.target:
            self.dfs_searcher.target = None
            self.bfs_searcher.target = None

        self.dfs_searcher.add_avoid(address)
        self.bfs_searcher.add_avoid(address)

    @locked
    def reset_searchers(self):
        if not self.symbolic_started():
            return

        for addr in self.searcher_tags:
            tt, func = self.searcher_tags[addr]
            func.remove_auto_address_tags_of_type(addr, tt)

        self.searcher_tags = {}
        self.dfs_searcher.target = None
        self.bfs_searcher.target = None
        self.dfs_searcher.avoid = []
        self.bfs_searcher.avoid = []

    @locked
    def async_run_dfs_searcher(self):
        if not self.symbolic_started():
            return

        if not self.dfs_searcher.ready_to_run():
            log_alert("SENinja: no target set for searcher")
            return

        timeout = self.executor.bncache.get_setting("exploration_timeout")
        timeout = int(timeout)

        def f(tb):
            start = time.time()
            def callback(s):
                if s is None:
                    return False
                tb.progress = "SENinja: running DFS @ %s" % hex(s.get_ip())
                if timeout > 0 and time.time() - start > timeout:
                    sys.stderr.write("SENinja: Timeout elapsed (%d sec)\n" % timeout)
                    return False
                if self.stop:
                    self.stop = False
                    return False
                return True

            self.dfs_searcher.run(step_callback=callback)
            self._sync_ui(self.executor._last_error == None)
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(self.bv, "SENinja: running DFS", f)
            background_task.start()

    @locked
    def async_run_bfs_searcher(self):
        if not self.symbolic_started():
            return

        if not self.bfs_searcher.ready_to_run():
            log_alert("SENinja: no target set for searcher")
            return

        timeout = self.executor.bncache.get_setting("exploration_timeout")
        timeout = int(timeout)

        def f(tb):
            start = time.time()
            def callback(s):
                if s is None:
                    return False
                tb.progress = "SENinja: running BFS @ %s" % hex(s.get_ip())
                if timeout > 0 and time.time() - start > timeout:
                    sys.stderr.write("SENinja: Timeout elapsed (%d sec)\n" % timeout)
                    return False
                if self.stop:
                    self.stop = False
                    return False
                return True

            self.bfs_searcher.run(callback)

            self._sync_ui(self.executor._last_error == None)
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(self.bv, "SENinja: running BFS", f)
            background_task.start()

    @locked
    def async_step(self):
        if not self.symbolic_started():
            return

        def f(tb):
            self.executor.execute_one()
            self._sync_ui(self.executor._last_error == None)
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(self.bv, "SENinja: stepping", f)
            background_task.start()

    @locked
    def async_continue_until_branch(self):
        if not self.symbolic_started():
            return

        timeout = self.executor.bncache.get_setting("exploration_timeout")
        timeout = int(timeout)

        def f(tb):
            start = time.time()
            k = len(self.executor.fringe.deferred)
            i = k
            count = 0
            while not self.stop and i == k:
                self.executor.execute_one()
                if not self.executor.state:
                    break

                if timeout > 0 and time.time() - start > timeout:
                    # Timeout elapsed
                    sys.stderr.write("SENinja: Timeout elapsed (%d sec)\n" % timeout)
                    break

                i = len(self.executor.fringe.deferred)
                ip = self.executor.state.get_ip()
                count = (count+1) % 20
                if count == 0:
                    self._set_colors()
                tb.progress = "SENinja: continue until branch: %s" % hex(ip)

            self._sync_ui(self.executor._last_error == None)
            self.running = False
            self.stop = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(
                self.bv, "SENinja: continue until branch", f)
            background_task.start()

    @locked
    def async_continue_until_address(self, address):
        if not self.symbolic_started():
            return

        timeout = self.executor.bncache.get_setting("exploration_timeout")
        timeout = int(timeout)

        address = get_address_after_merge(self.bv, address)

        def f(tb):
            ip = self.executor.state.get_ip()
            start = time.time()

            count = 0
            while not self.stop and ip != address:
                self.executor.execute_one()
                if not self.executor.state:
                    break

                if timeout > 0 and time.time() - start > timeout:
                    # Timeout elapsed
                    sys.stderr.write("SENinja: Timeout elapsed (%d sec)\n" % timeout)
                    break

                ip = self.executor.state.get_ip()
                count = (count+1) % 20
                if count == 0:
                    self._set_colors()
                tb.progress = "SENinja: continue until address: %s" % hex(ip)

            self._sync_ui(self.executor._last_error == None)
            self.running = False
            self.stop = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(
                self.bv, "SENinja: continue until address", f)
            background_task.start()

    @locked
    def async_merge_states(self, address):
        # merge all states at address and put them in current state. Current state must be at address
        if not self.symbolic_started():
            return

        if self.executor.state.get_ip() != address:
            log_alert("SENinja: current state is not at this address")
            return

        to_be_merged_all = self.executor.fringe.get_all_deferred_by_address(
            address)
        if to_be_merged_all is None:
            log_alert("SENinja: no deferred state at this address")
            return

        mergeable, not_mergeable = self.executor.extract_mergeable_with_current_state(
            to_be_merged_all)
        if len(not_mergeable) > 0:
            sys.stderr.write(
                "SENinja [warning]: %d states was not merged since they deviate from the current state after executing the current instruction\n" % len(not_mergeable))
            self.executor.fringe._deferred[address] = not_mergeable

        if len(mergeable) == 0:
            return
        to_be_merged = mergeable

        def f(tb):
            tot = len(to_be_merged)
            i = 0
            for s in to_be_merged:
                self.executor.state.merge(s)
                i += 1
                tb.progress = "SENinja: merging states %d/%d" % (i, tot)

            self._delete_comment_for_address(address)
            self._sync_ui()
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(self.bv, "SENinja: merging states", f)
            background_task.start()

    @locked
    def async_change_current_state(self, address):
        if not self.symbolic_started():
            return

        states = self.executor.fringe.get_list_deferred_by_address(address)
        if len(states) == 0:
            log_alert("SENinja: no such deferred state")
            return
        if len(states) == 1:
            state = self.executor.fringe.get_deferred_by_address(address)
        else:
            state_idx = get_choice_input(
                "Select state", "states", list(map(str, states)))
            state = self.executor.fringe.get_deferred_by_address(
                address, state_idx)

        self._delete_comment_for_address(address)
        self.executor.set_current_state(state)
        self._sync_ui(delta=False)

    @locked
    def async_save_active_state(self):
        if not self.symbolic_started():
            return

        def f(tb):
            saved_state = self.executor.state.copy()
            self.executor.put_in_deferred(saved_state)

            self._sync_ui(delta=False)
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(
                self.bv, "SENinja: saving current state", f)
            background_task.start()

    @locked
    def async_change_active_state_ip(self, address):
        if not self.symbolic_started():
            return

        def f(tb):
            state = self.executor.state
            state.set_ip(address)
            func_name = self.executor.bncache.get_function_name(address)
            state.llil_ip = self.executor.bncache.get_llil_address(
                func_name, address)

            self.executor.state = None
            self.executor.set_current_state(state)

            self._sync_ui(delta=False)
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()
            background_task = UIBackgroundTask(
                self.bv, "SENinja: changing current state", f)
            background_task.start()

    @locked
    def async_reset_se(self):
        if not self.symbolic_started():
            return

        def f(tb):
            for addr in self.searcher_tags:
                tag, func = self.searcher_tags[addr]
                func.remove_auto_address_tags_of_type(addr, tag)
            self.searcher_tags = dict()

            self._set_colors(reset=True)
            self.executor = None
            self.running = False
            self.widget.enableAll()

        if not self.running:
            self.running = True
            self.widget.disableAll()

            self._reset_ui()
            background_task = UIBackgroundTask(
                self.bv, "SENinja: resetting symbolic execution", f)
            background_task.start()

    @locked
    def launch_argv_dialog(self):
        if self.executor is None:
            return

        # This is an hack: keep a pointer to the widget before spawning the dialog
        #                  because otherwise is won't be accessible
        widget = self.widget

        d = GetArgvDialog(self.executor.state)
        d.exec_()
        widget.updateStateSignal.emit(self.executor.state)
