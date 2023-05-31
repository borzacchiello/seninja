from binaryninja import BackgroundTaskThread
from binaryninja.interaction import (
    show_message_box,
    get_int_input,
)
from binaryninjaui import (
    GlobalAreaWidget,
    UIActionHandler
)
from PySide6.QtCore import QMimeData
from PySide6.QtWidgets import (
    QApplication,
    QGridLayout,
    QSizePolicy,
    QMenu,
    QPushButton
)

from ..utility.expr_wrap_util import symbolic, split_bv_in_list
from ..expr.bitvector import BVS, BVV
from .hexview import HexViewWidget

def _normalize_tab_name(tab_name):
    return tab_name[:tab_name.find("(")-1]


class MemoryViewBT(BackgroundTaskThread):
    def __init__(self, msg, mw, callback, pars):
        BackgroundTaskThread.__init__(self, msg, False)
        self.mw = mw
        self.pars = pars
        self.callback = callback

    def run(self):
        self.mw.setEnabled(False)
        self.callback(*self.pars)
        self.mw.setEnabled(True)


class MemoryView(GlobalAreaWidget):

    def __init__(self, name, data, bnwidgets):
        GlobalAreaWidget.__init__(self, name)

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)
        self.data = data
        self.bnwidgets = bnwidgets

        self.current_state = None
        self.arch = None
        self.address_start = None
        self.size = 512
        self.changes = set()
        self.tab_name = None

        self.monitor_history = list()

        self.symb_idx = 0

        self._layout = QGridLayout()
        self.button = QPushButton("Monitor Memory")
        self.button.setStyleSheet("margin-left: 10px;")
        self.button.clicked.connect(self._condom_async(
            self, self.on_monitor_button_click))
        self.back_button = QPushButton("Back")
        self.back_button.setStyleSheet("margin-right: 10px;")
        self.back_button.clicked.connect(self._condom_async(
            self, self.on_back_click))

        self.hexWidget = HexViewWidget(
            menu_handler=self.on_customContextMenuRequested)
        self.hexWidget.data_edited.connect(self._handle_data_edited)
        self.hexWidget.setEnabled(False)

        self._layout.addWidget(self.button, 0, 0, 1, 4)
        self._layout.addWidget(self.back_button, 0, 4, 1, 1)
        self._layout.addWidget(self.hexWidget, 2, 0, 1, 5)
        self._layout.setContentsMargins(0, 0, 0, 0)
        self.setLayout(self._layout)

    def _monitor_changes(self, address, size):
        if symbolic(address):
            self.changes.clear()
            self.changes.add((
                self.address_start, self.address_start + self.size
            ))
            return

        address = address.value
        if (
            self.address_start + self.size >= address and
            self.address_start <= address + size
        ):
            to_monitor_min = max(self.address_start,
                                 address) - self.address_start
            to_monitor_max = min(self.address_start + self.size,
                                 address + size) - self.address_start
            self.changes.add((to_monitor_min, to_monitor_max))

    def on_monitor_button_click(self):
        if self.current_state is None:
            return

        address = get_int_input("Memory address", "Set Memory Monitor")
        if address is None:
            return
        address = address & 0xffffffffffffffff  # signed to unsigned
        self.monitor_history.append(address)

        self.hexWidget.setEnabled(True)
        self.address_start = address
        self.size = 512
        self.current_state.mem.register_store_hook(self._monitor_changes)
        self.update_mem(self.current_state)

        # FIXME: find a better way. This is necessary to update the headers
        self.hexWidget.hide()
        self.hexWidget.show()

    def on_back_click(self):
        if self.current_state is None:
            return

        if len(self.monitor_history) < 2:
            return

        self.monitor_history.pop()
        address = self.monitor_history[-1]

        self.hexWidget.setEnabled(True)
        self.address_start = address
        self.size = 512
        self.current_state.mem.register_store_hook(self._monitor_changes)
        self.update_mem(self.current_state)

        # FIXME: find a better way. This is necessary to update the headers
        self.hexWidget.hide()
        self.hexWidget.show()

    def init(self, arch, state):
        self.arch = arch
        self.update_mem(state)

    def update_mem(self, state):
        self.current_state = state
        if self.address_start is None:
            return
        self.changes.clear()
        data = {}
        for i in range(self.size):
            if not state.mem.is_mapped(self.address_start + i):
                val = "__"
            else:
                b = state.mem.load(self.address_start + i, 1)
                val = ".."
                if isinstance(b, BVV):
                    val = "{:02x}".format(b.value)
            data[i] = val

        self.hexWidget.full_data_changed.emit(
            self.address_start, data, self.size
        )

    def update_mem_delta(self, state):
        self.current_state = state
        if self.address_start is None:
            return

        load_cache = {}
        for begin, end in self.changes:
            for i in range(begin, end):
                if not state.mem.is_mapped(self.address_start + i):
                    val = "__"
                else:
                    if i in load_cache:
                        b = load_cache[i]
                    else:
                        b = state.mem.load(self.address_start + i, 1)
                        load_cache[i] = b
                    val = ".."
                    if isinstance(b, BVV):
                        val = "{:02x}".format(b.value)
                self.hexWidget.single_data_changed.emit(i, val)
        # self.hexWidget.view.viewport().update()
        self.changes.clear()

    def reset(self):
        self.tab_name = None
        self.current_state = None
        self.address_start = None
        self.size = None
        self.hexWidget.full_data_changed.emit(
            0, {}, 0
        )
        self.hexWidget._hsm.clearSelection()

    def _handle_data_edited(self, offset, value):
        if not self.current_state or not self.address_start:
            return

        self.current_state.mem.store(
            self.address_start + offset, BVV(value, 8))
        # self.hexWidget.single_data_changed.emit(address - self.address_start, hex(value)[2:])

    def _show_expression(self, address, expr):
        show_message_box("Expression at %s" %
                         hex(address), str(expr.z3obj.sexpr()))

    def _evaluate_with_solver(self, address, expr):
        val = ""
        if not self.current_state.solver.symbolic(expr):
            new_expr = self.current_state.solver.evaluate(expr)
            self.current_state.mem.store(address, new_expr)
            self.changes.add(
                (
                    address - self.address_start,
                    address-self.address_start+new_expr.size // 8
                )
            )
            self.update_mem_delta(self.current_state)
            show_message_box(
                "Expression at %s" % hex(address),
                "The value was indeed concrete! State modified"
            )
        else:
            val = self.current_state.solver.evaluate(expr).value
            show_message_box("Value at %s (with solver):" %
                             hex(address), hex(val))

    def _evaluate_upto_with_solver(self, address, expr):
        val = ""
        if not self.current_state.solver.symbolic(expr):
            new_expr = self.current_state.solver.evaluate(expr)
            self.current_state.mem.store(address, new_expr)
            self.changes.add(
                (
                    address - self.address_start,
                    address-self.address_start+new_expr.size // 8
                )
            )
            self.update_mem_delta(self.current_state)
            show_message_box(
                "Expression at %s" % hex(address),
                "The value was indeed concrete! State modified"
            )
        else:
            n_eval = get_int_input("How many values (upto) ?", "Number of distinct values")
            if n_eval is None:
                return
            r = ""
            for i, v in enumerate(self.current_state.solver.evaluate_upto(expr, n_eval)):
                r += "solution %d: %s\n" % (i, hex(v.value))

            show_message_box("Value at %s (with solver):" %
                             hex(address), r)

    def _concretize(self, address, expr):
        new_expr = self.current_state.solver.evaluate(expr)
        self.current_state.mem.store(address, new_expr)
        self.current_state.solver.add_constraints(
            expr == new_expr
        )
        self.changes.add(
            (
                address - self.address_start,
                address - self.address_start+new_expr.size // 8
            )
        )
        self.update_mem(self.current_state)

    def _concretize_ascii_str(self, address, expr):
        extra_constraints = []
        for i in range(expr.size // 8):
            b = expr.Extract(i*8+7, i*8)
            extra_constraints.extend(
                [b <= 0x7e, b >= 0x20]
            )
        if not self.current_state.solver.satisfiable(
            extra_constraints
        ):
            show_message_box(
                "Info", "The selected memory is not an ascii str (unsat)")
            return
        new_expr = self.current_state.solver.evaluate(
            expr, extra_constraints
        )
        self.current_state.mem.store(address, new_expr)
        self.current_state.solver.add_constraints(
            expr == new_expr
        )
        self.changes.add(
            (
                address - self.address_start,
                address - self.address_start+new_expr.size // 8
            )
        )
        self.update_mem_delta(self.current_state)

    def _make_symbolic(self, address, size):
        buff = BVS("b_ui_mem_%d" % self.symb_idx, size * 8)
        self.current_state.mem.store(address, buff)
        self.current_state.symbolic_buffers.append(
            (buff, address, "")
        )
        self.changes.add(
            (
                address - self.address_start,
                size
            )
        )
        self.symb_idx += 1
        self.update_mem_delta(self.current_state)
        self.bnwidgets.BW.onNewBufferSignal.emit(self.current_state)
        self.update_mem(self.current_state)

    def _copy_big_endian(self, expr):
        mime = QMimeData()
        mime.setText(hex(expr.value))
        QApplication.clipboard().setMimeData(mime)

    def _copy_little_endian(self, expr):
        mime = QMimeData()
        expr_bytes = split_bv_in_list(expr, 8)
        res = 0
        i = 0
        for el in reversed(expr_bytes):
            res += el.value << i*8
            i += 1
        mime.setText(hex(res))
        QApplication.clipboard().setMimeData(mime)

    def _copy_string(self, expr):
        mime = QMimeData()
        expr_bytes = split_bv_in_list(expr, 8)
        res = ""
        for el in reversed(expr_bytes):
            res += chr(el.value) if el.value >= 32 and el.value <= 126 else "."

        mime.setText(res)
        QApplication.clipboard().setMimeData(mime)

    def _copy_expression(self, expr):
        mime = QMimeData()
        mime.setText(str(expr.z3obj.sexpr()))
        QApplication.clipboard().setMimeData(mime)

    def _copy_binary(self, expr):
        mime = QMimeData()
        expr_bytes = split_bv_in_list(expr, 8)
        res = "\""
        for el in reversed(expr_bytes):
            res += "\\x{:02x}".format(el.value)
        res += "\""

        mime.setText(res)
        QApplication.clipboard().setMimeData(mime)

    @staticmethod
    def _condom(f, *pars):
        def g():
            f(*pars)
        return g

    @staticmethod
    def _condom_async(mw, f, *pars):
        def g():
            bt = MemoryViewBT("MemoryView background task...", mw, f, pars)
            bt.start()
        return g

    def on_customContextMenuRequested(self, qpoint):
        if self.current_state is None:
            return
        menu = QMenu(self)

        sel_start = self.hexWidget._hsm.start
        sel_end = self.hexWidget._hsm.end
        if sel_start is None:
            return

        if not self.current_state.mem.is_mapped(
                self.address_start + sel_start):
            return
        if not self.current_state.mem.is_mapped(
                self.address_start + sel_end):
            return

        expr = self.current_state.mem.load(
            sel_start + self.address_start,
            sel_end - sel_start + 1
        )

        if symbolic(expr):
            a = menu.addAction("Show expression")
            a.triggered.connect(MemoryView._condom(
                self._show_expression, sel_start + self.address_start, expr))
            a = menu.addAction("Evaluate with solver")
            a.triggered.connect(MemoryView._condom_async(
                self, self._evaluate_with_solver, sel_start + self.address_start, expr))
            a = menu.addAction("Evaluate with solver (upto)")
            a.triggered.connect(MemoryView._condom_async(
                self, self._evaluate_upto_with_solver, sel_start + self.address_start, expr))
            a = menu.addAction("Concretize")
            a.triggered.connect(MemoryView._condom_async(
                self, self._concretize, sel_start + self.address_start, expr))
            a = menu.addAction("Concretize (ascii str)")
            a.triggered.connect(MemoryView._condom_async(
                self, self._concretize_ascii_str, sel_start + self.address_start, expr))
            a = menu.addAction("Copy expression")
            a.triggered.connect(MemoryView._condom(
                self._copy_expression, expr))
        else:
            a = menu.addAction("Make symbolic")
            a.triggered.connect(MemoryView._condom(
                self._make_symbolic, sel_start + self.address_start, sel_end - sel_start + 1))
            copy_menu = menu.addMenu("Copy...")
            a = copy_menu.addAction("Copy Little Endian")
            a.triggered.connect(MemoryView._condom(
                self._copy_little_endian, expr))
            a = copy_menu.addAction("Copy Big Endian")
            a.triggered.connect(MemoryView._condom(
                self._copy_big_endian, expr))
            a = copy_menu.addAction("Copy String")
            a.triggered.connect(MemoryView._condom(self._copy_string, expr))
            a = copy_menu.addAction("Copy Binary")
            a.triggered.connect(MemoryView._condom(self._copy_binary, expr))

        return menu

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        elif self.tab_name is None:
            return False
        elif _normalize_tab_name(view_frame.getTabName()) != self.tab_name:
            return False
        return True

    def notifyViewChanged(self, view_frame):
        if view_frame is None:
            pass
        else:
            pass  # implement this

    def contextMenuEvent(self, event):
        self.m_contextMenuManager.show(self.m_menu, self.actionHandler)
