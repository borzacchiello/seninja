from binaryninja import BackgroundTaskThread
from binaryninja.interaction import (
    show_message_box,
    get_int_input,
)
from binaryninjaui import (
    UIActionHandler
)
from PySide6 import QtCore
from PySide6.QtCore import QMimeData
from PySide6.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QMenu,
    QWidget,
    QComboBox
)

from ..utility.expr_wrap_util import symbolic, split_bv_in_list
from ..expr.bitvector import BVS, BVV
from .qmemview import QMemView

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

gMemPerTab = {}

class MemoryViewData(object):
    def __init__(self):
        self.current_state = None
        self.regions       = None

class MemoryView(QWidget):
    def __init__(self, parent):
        QWidget.__init__(self, parent)

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)

        self.tabname  = ""
        self.data     = MemoryViewData()
        self.symb_idx = 0

        self.layout    = QVBoxLayout()
        self.memWidget = QMemView(
            addr=0,
            size=0,
            dataCallback=None)
        self.regionSelector = QComboBox()
        self.regionSelector.currentIndexChanged.connect(self.regionSelectorChanged)

        self.memWidget.customMenu = self.on_customContextMenuRequested

        self.layout.addWidget(self.regionSelector)
        self.layout.addWidget(self.memWidget)
        self.setLayout(self.layout)

    def regionSelectorChanged(self, i):
        if self.data.current_state is None:
            return
        regions = self.data.current_state.mem.get_regions()
        if i >= len(regions):
            return

        addr, size = regions[i]
        self.memWidget.addr = addr
        self.memWidget.size = size
        self.memWidget.updateScrollbars()
        self.memWidget.viewport().update()

    def stateReset(self):
        self.data = MemoryViewData()
        self.memWidget.addr = 0
        self.memWidget.size = 0
        self.memWidget.dataCallback = None
        self.memWidget.updateScrollbars()
        self.memWidget.viewport().update()
        self.regionSelector.clear()

    def _init_internal(self):
        self.stateUpdate(self.data.current_state)

    def stateInit(self, arch, state):
        self.data = MemoryViewData()
        self.data.current_state = state
        self._init_internal()

    def stateUpdate(self, state):
        regions = state.mem.get_regions()
        if self.data.regions != regions:
            self.regionSelector.clear()
            for addr, size in regions:
                self.regionSelector.addItem(
                    "0x%016x -> 0x%016x" % (addr, addr+size))
            self.data.regions = regions
        if len(regions) > 0:
            addr, size = regions[0]
            self.memWidget.addr = addr
            self.memWidget.size = size

            def callback(addr):
                v = state.mem.load(addr, 1)
                if isinstance(v, BVV):
                    return "%02x" % v.value
                return ".."
            self.memWidget.dataCallback = callback
            self.memWidget.updateScrollbars()
            self.memWidget.viewport().update()
        self.data.current_state = state

    def _show_expression(self, address, expr):
        show_message_box("Expression at %s" %
                         hex(address), str(expr.z3obj.sexpr()))

    def _evaluate_with_solver(self, address, expr):
        val = ""
        if not self.data.current_state.solver.symbolic(expr):
            new_expr = self.data.current_state.solver.evaluate(expr)
            self.data.current_state.mem.store(address, new_expr)
            self.stateUpdate(self.data.current_state)
            show_message_box(
                "Expression at %s" % hex(address),
                "The value was indeed concrete! State modified"
            )
        else:
            val = self.data.current_state.solver.evaluate(expr).value
            show_message_box("Value at %s (with solver):" %
                             hex(address), hex(val))

    def _evaluate_upto_with_solver(self, address, expr):
        if not self.data.current_state.solver.symbolic(expr):
            new_expr = self.data.current_state.solver.evaluate(expr)
            self.data.current_state.mem.store(address, new_expr)
            self.stateUpdate(self.data.current_state)
            show_message_box(
                "Expression at %s" % hex(address),
                "The value was indeed concrete! State modified"
            )
        else:
            n_eval = get_int_input("How many values (upto) ?", "Number of distinct values")
            if n_eval is None:
                return
            r = ""
            for i, v in enumerate(self.data.current_state.solver.evaluate_upto(expr, n_eval)):
                r += "solution %d: %s\n" % (i, hex(v.value))

            show_message_box("Value at %s (with solver):" %
                             hex(address), r)

    def _concretize(self, address, expr):
        new_expr = self.data.current_state.solver.evaluate(expr)
        self.data.current_state.mem.store(address, new_expr)
        self.data.current_state.solver.add_constraints(
            expr == new_expr
        )

    def _concretize_ascii_str(self, address, expr):
        extra_constraints = []
        for i in range(expr.size // 8):
            b = expr.Extract(i*8+7, i*8)
            extra_constraints.extend(
                [b <= 0x7e, b >= 0x20]
            )
        if not self.data.current_state.solver.satisfiable(
            extra_constraints
        ):
            show_message_box(
                "Info", "The selected memory is not an ascii str (unsat)")
            return
        new_expr = self.data.current_state.solver.evaluate(
            expr, extra_constraints
        )
        self.data.current_state.mem.store(address, new_expr)
        self.data.current_state.solver.add_constraints(
            expr == new_expr
        )
        self.stateUpdate(self.data.current_state)

    def _make_symbolic(self, address, size):
        buff = BVS("b_ui_mem_%d" % self.symb_idx, size * 8)
        self.data.current_state.mem.store(address, buff)
        self.data.current_state.symbolic_buffers.append(
            (buff, address, "")
        )
        self.symb_idx += 1
        self.stateUpdate(self.data.current_state)

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

    def on_customContextMenuRequested(self):
        if self.data.current_state is None:
            return
        menu = QMenu(self)

        selStart, selSize = self.memWidget.getSelection()
        if selSize == 0:
            return

        if not self.data.current_state.mem.is_mapped(
                selStart):
            return
        if not self.data.current_state.mem.is_mapped(
                selStart + selSize):
            return

        expr = self.data.current_state.mem.load(
            selStart,
            selSize
        )

        if symbolic(expr):
            a = menu.addAction("Show expression")
            a.triggered.connect(MemoryView._condom(
                self._show_expression, selStart, expr))
            a = menu.addAction("Evaluate with solver")
            a.triggered.connect(MemoryView._condom_async(
                self, self._evaluate_with_solver, selStart, expr))
            a = menu.addAction("Evaluate with solver (upto)")
            a.triggered.connect(MemoryView._condom_async(
                self, self._evaluate_upto_with_solver, selStart, expr))
            a = menu.addAction("Concretize")
            a.triggered.connect(MemoryView._condom_async(
                self, self._concretize, selStart, expr))
            a = menu.addAction("Concretize (ascii str)")
            a.triggered.connect(MemoryView._condom_async(
                self, self._concretize_ascii_str, selStart, expr))
            a = menu.addAction("Copy expression")
            a.triggered.connect(MemoryView._condom(
                self._copy_expression, expr))
        else:
            a = menu.addAction("Make symbolic")
            a.triggered.connect(MemoryView._condom(
                self._make_symbolic, selStart, selSize))
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
        return True

    def notifytab(self, newName):
        if newName != self.tabname:
            if self.tabname != "":
                gMemPerTab[self.tabname] = self.data
                self.stateReset()

            if newName in gMemPerTab:
                self.data = gMemPerTab[newName]
                self._init_internal()
        self.tabname = newName
