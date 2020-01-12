from binaryninja.interaction import (
    show_message_box,
    get_int_input,
    get_choice_input
)
from binaryninjaui import (
    DockHandler,
    DockContextHandler,
    getMonospaceFont,
    UIActionHandler
)
from PySide2 import QtCore
from PySide2.QtCore import Qt, QMimeData
from PySide2.QtGui import QBrush, QColor, QStandardItemModel, QStandardItem
from PySide2.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QWidget,
    QComboBox,
    QTableWidget,
    QTableWidgetItem,
    QStackedWidget,
    QMenu,
    QTableView,
    QPushButton,
    QHeaderView
)

from ..utility.expr_wrap_util import symbolic, split_bv_in_list
from ..expr.bitvector import BVS, BVV
from .hexview import HexViewWidget

class MemoryView(QWidget, DockContextHandler):

    def __init__(self, parent, name, data):
        QWidget.__init__(self, parent)
        DockContextHandler.__init__(self, self, name)

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)
        self.data = data
        self.parent = parent

        self.current_state = None
        self.arch = None
        self.address_start = None
        self.size = None
        self.changes = set()

        self.symb_idx = 0

        self._layout = QVBoxLayout()
        self.button = QPushButton("Monitor Memory")
        self.button.clicked.connect(self.on_monitor_button_click)

        self.hexWidget = HexViewWidget(menu_handler=self.on_customContextMenuRequested)
        self.hexWidget.data_edited.connect(self._handle_data_edited)
        self.hexWidget.setEnabled(False)

        self._layout.addWidget(self.button)
        self._layout.addWidget(self.hexWidget)
        self._layout.setContentsMargins(0,0,0,0)

        self.setMaximumWidth(self.hexWidget.optimal_width + 25)

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
            to_monitor_min = max(self.address_start, address) - self.address_start
            to_monitor_max = min(self.address_start + self.size, address + size) - self.address_start
            self.changes.add((to_monitor_min, to_monitor_max))

    def on_monitor_button_click(self):
        if self.current_state is None:
            return

        address = get_int_input("Memory address", "Set Memory Monitor")
        if address is None: return

        self.hexWidget.setEnabled(True)
        self.address_start = address
        self.size = 512
        self.current_state.mem.register_store_hook(self._monitor_changes)
        self.update_mem(self.current_state)

    def set_arch(self, arch):
        self.arch = arch
    
    def update_mem(self, state):
        self.current_state = state
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
        self.current_state = None
        self.address_start = None
        self.size = None
        self.hexWidget.full_data_changed.emit(
            0, {}, 0
        )
    
    def _handle_data_edited(self, offset, value):
        if not self.current_state or not self.address_start:
            return
        
        self.current_state.mem.store(self.address_start + offset, BVV(value, 8))
        # self.hexWidget.single_data_changed.emit(address - self.address_start, hex(value)[2:])

    def _show_reg_expression(self, address, expr):
        show_message_box("Expression at %s" % hex(address), str(expr.z3obj))
    
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
            show_message_box("Value at %s (with solver):" % hex(address), hex(val))
    
    def _concretize(self, address, expr):
        new_expr = self.current_state.solver.evaluate(expr)
        res = get_choice_input(
            "Concretize *%s to %s?" % (hex(address), hex(new_expr.value)),
            "Concretize",
            ["Yes", "No"]
        )
        if res == 0:
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
        expr = BVS("symbol_injected_through_ui_mem_%d" % self.symb_idx, size*8)
        self.current_state.mem.store(address, expr)
        self.changes.add(
            (
                address - self.address_start,
                size
            )
        )
        self.symb_idx += 1
        self.update_mem_delta(self.current_state)
    
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
            i+=1
        mime.setText(hex(res))
        QApplication.clipboard().setMimeData(mime)
    
    @staticmethod
    def _condom(f, *pars):
        def g():
            f(*pars)
        return g
    
    def on_customContextMenuRequested(self, qpoint):
        if self.current_state is None:
            return
        menu = QMenu(self)
        index = self.hexWidget.view.indexAt(qpoint)

        sel_start = self.hexWidget._hsm.start
        sel_end   = self.hexWidget._hsm.end
        if sel_start is None:
            return

        expr = self.current_state.mem.load(
            sel_start + self.address_start, 
            sel_end - sel_start + 1
        )

        if symbolic(expr):
            a = menu.addAction("Show reg expression")
            a.triggered.connect(MemoryView._condom(self._show_reg_expression, sel_start + self.address_start, expr))
            a = menu.addAction("Evaluate with solver")
            a.triggered.connect(MemoryView._condom(self._evaluate_with_solver, sel_start + self.address_start, expr))
            a = menu.addAction("Concretize")
            a.triggered.connect(MemoryView._condom(self._concretize, sel_start + self.address_start, expr))
        else:
            a = menu.addAction("Make symbolic")
            a.triggered.connect(MemoryView._condom(self._make_symbolic, sel_start + self.address_start, sel_end - sel_start + 1))
            copy_menu = menu.addMenu("Copy...")
            a = copy_menu.addAction("Copy Little Endian")
            a.triggered.connect(MemoryView._condom(self._copy_little_endian, expr))
            a = copy_menu.addAction("Copy Big Endian")
            a.triggered.connect(MemoryView._condom(self._copy_big_endian, expr))

        return menu

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        else:
            return True

    def notifyViewChanged(self, view_frame):
        if view_frame is None:
            pass
        else:
            pass  # implement this
            # self.bv = view_frame.actionContext().binaryView
            # self.filename = self.bv.file.original_filename

    def contextMenuEvent(self, event):
        self.m_contextMenuManager.show(self.m_menu, self.actionHandler)
