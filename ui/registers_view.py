from binaryninja.interaction import (
    show_message_box,
    get_int_input,
    get_choice_input
)
from binaryninjaui import (
    SidebarWidget,
    SidebarWidgetType,
    SidebarWidgetLocation,
    SidebarContextSensitivity,
    getMonospaceFont,
    UIActionHandler,
    getThemeColor,
    ThemeColor
)
from PySide6 import QtCore
from PySide6.QtCore import (
    Qt,
    QRectF,
    QMimeData
)
from PySide6.QtGui import (
    QPainter,
    QBrush,
    QColor,
    QFont,
    QImage
)
from PySide6.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QWidget,
    QTableWidget,
    QTableWidgetItem,
    QMenu
)

from ..utility.expr_wrap_util import symbolic
from ..expr.bitvector import BVS, BVV

def _makewidget(parent, val, center=False):
    out = QTableWidgetItem(str(val))
    out.setFlags(Qt.ItemIsEnabled)
    out.setFont(getMonospaceFont(parent))
    if center:
        out.setTextAlignment(Qt.AlignCenter)
    return out

gRegsPerTab = {}

class RegisterData(object):
    def __init__(self):
        self.arch          = None
        self.current_state = None
        self.symb_idx      = 0
        self.reg_to_index  = dict()
        self.index_to_reg  = dict()
        self.reg_cache     = dict()

class RegisterWidget(QWidget):
    dirty_color      = QBrush(getThemeColor(ThemeColor.OrangeStandardHighlightColor))
    expression_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
    symbolic_color   = QBrush(getThemeColor(ThemeColor.BlueStandardHighlightColor))
    no_color         = QBrush(getThemeColor(ThemeColor.WhiteStandardHighlightColor))

    def __init__(self, parent):
        QWidget.__init__(self, parent)
        self.tabname = ""
        self.data    = RegisterData()

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)

        self.layout = QVBoxLayout()

        # Set up register table
        self.table = QTableWidget()
        self.table.setColumnCount(2)
        self.table.setHorizontalHeaderLabels(['Register', 'Value'])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)

        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.on_customContextMenuRequested)
        self.table.doubleClicked.connect(self.on_doubleClick)

        self.layout.addWidget(self.table)
        self.setLayout(self.layout)

    def stateReset(self):
        self.data = RegisterData()
        self.table.setRowCount(0)

    def _init_internal(self):
        if self.data.arch is None:
            return
        regs = self.data.arch.reg_names()

        self.table.setRowCount(len(regs))
        for i, reg in enumerate(regs):
            self.data.reg_to_index[reg] = i
            self.data.index_to_reg[i] = reg
            self.table.setItem(i, 0, _makewidget(self, reg))
            self.table.setItem(i, 1, _makewidget(self, ""))
        self.stateUpdate(self.data.current_state)

    def stateInit(self, arch, state):
        self.data.arch = arch
        self.data.current_state = state
        self._init_internal()

    def set_reg_value(self, reg, value, color=None):
        assert self.data.arch is not None

        idx = self.data.reg_to_index[reg]

        if symbolic(value):
            if isinstance(value, BVS):
                val_str = value.name
                if color is None:
                    color = RegisterWidget.symbolic_color
            else:
                val_str = "< symbolic expression >"
                if color is None:
                    color = RegisterWidget.expression_color
        else:
            val_str = "0x{obj:0{width}x}".format(
                obj=value.value,
                width=(value.size+3) // 4
            )

        self.data.reg_cache[reg] = val_str
        table_item = self.table.item(idx, 1)
        table_item.setText(val_str)
        if color is not None:
            table_item.setForeground(color)
        else:
            table_item.setForeground(self.no_color)

    def stateUpdate(self, state):
        self.data.current_state = state
        for reg in self.data.reg_to_index:
            val = getattr(state.regs, reg)
            self.set_reg_value(reg, val)

    # right click menu
    def on_customContextMenuRequested(self, pos):
        item = self.table.itemAt(pos)
        if item is None:
            return
        row_idx = item.row()

        if self.data.index_to_reg[row_idx] == self.data.arch.getip_reg():
            return

        expr = getattr(self.data.current_state.regs, self.data.index_to_reg[row_idx])

        menu = QMenu()
        show_reg_expr = menu.addAction(
            "Show reg expression") if not isinstance(expr, BVV) else None
        make_reg_symb = menu.addAction(
            "Make reg symbolic") if isinstance(expr, BVV) else None
        set_reg_value = menu.addAction("Set reg value")
        eval_with_sol = menu.addAction(
            "Evaluate with solver") if not isinstance(expr, BVV) else None
        eval_upto_with_sol = menu.addAction(
            "Evaluate upto with solver") if not isinstance(expr, BVV) else None
        concretize = menu.addAction(
            "Concretize") if not isinstance(expr, BVV) else None
        copy = menu.addAction("Copy to clipboard") if not isinstance(
            expr, BVS) else None
        bind_to_buffer = menu.addAction("Bind to symbolic buffer")

        action = menu.exec_(self.table.viewport().mapToGlobal(pos))
        if action is None:
            return

        if action == bind_to_buffer:
            buffer_names = [
                b[0].name for b in self.data.current_state.symbolic_buffers]
            if len(buffer_names) == 0:
                return
            buff_id = get_choice_input(
                "Select a buffer", "choices", buffer_names)
            address = self.data.current_state.symbolic_buffers[buff_id][1]
            buff_p = BVV(address,
                         self.data.current_state.arch.bits())
            setattr(self.data.current_state.regs,
                    self.data.index_to_reg[row_idx],
                    buff_p)
            self.set_reg_value(
                self.data.index_to_reg[row_idx], buff_p, RegisterWidget.dirty_color)
        if action == show_reg_expr:
            show_message_box("Reg Expression", str(expr.z3obj.sexpr()))
        if action == make_reg_symb:
            new_expr = BVS('symb_injected_through_ui_%d' %
                           self.data.symb_idx, expr.size)
            setattr(self.data.current_state.regs,
                    self.data.index_to_reg[row_idx], new_expr)
            self.set_reg_value(
                self.data.index_to_reg[row_idx], new_expr, RegisterWidget.dirty_color)
            self.data.symb_idx += 1
        if action == set_reg_value:
            self.on_doubleClick(item)
        if action == eval_with_sol:
            expr = getattr(self.data.current_state.regs, self.data.index_to_reg[row_idx])
            if not self.data.current_state.solver.symbolic(expr):
                new_expr = self.data.current_state.solver.evaluate(expr)
                setattr(self.data.current_state.regs,
                        self.data.index_to_reg[row_idx], new_expr)
                self.set_reg_value(
                    self.data.index_to_reg[row_idx], new_expr, RegisterWidget.dirty_color)
                show_message_box(
                    "Reg Value (with solver)",
                    "The value was indeed concrete! State modified"
                )
            else:
                show_message_box(
                    "Reg Value (with solver)",
                    hex(self.data.current_state.solver.evaluate(expr).value)
                )
        if action == eval_upto_with_sol:
            expr = getattr(self.data.current_state.regs, self.data.index_to_reg[row_idx])
            if not self.data.current_state.solver.symbolic(expr):
                new_expr = self.data.current_state.solver.evaluate(expr)
                setattr(self.data.current_state.regs,
                        self.data.index_to_reg[row_idx], new_expr)
                self.set_reg_value(
                    self.data.index_to_reg[row_idx], new_expr, RegisterWidget.dirty_color)
                show_message_box(
                    "Reg Value (with solver)",
                    "The value was indeed concrete! State modified"
                )
            else:
                n_eval = get_int_input("How many values (upto) ?", "Number of distinct values")
                if n_eval is None:
                    return
                r = ""
                for i, v in enumerate(self.data.current_state.solver.evaluate_upto(expr, n_eval)):
                    r += "solution %d: %s\n" % (i, hex(v.value))
                show_message_box(
                    "Reg Value (with solver)",
                    r
                )
        if action == concretize:
            expr = getattr(self.data.current_state.regs, self.data.index_to_reg[row_idx])
            new_expr = self.data.current_state.solver.evaluate(expr)
            res = get_choice_input(
                "Concretize %s to %s?" % (
                    self.data.index_to_reg[row_idx], hex(new_expr.value)),
                "Concretize",
                ["Yes", "No"]
            )
            if res == 0:
                setattr(self.data.current_state.regs,
                        self.data.index_to_reg[row_idx], new_expr)
                self.data.current_state.solver.add_constraints(
                    expr == new_expr
                )
                self.set_reg_value(
                    self.data.index_to_reg[row_idx], new_expr, RegisterWidget.dirty_color)

        if action == copy:
            mime = QMimeData()
            if isinstance(expr, BVV):
                mime.setText(hex(expr.value))
            else:
                mime.setText(str(expr.z3obj.sexpr()))
            QApplication.clipboard().setMimeData(mime)

    # double click event
    def on_doubleClick(self, item):
        row_idx = item.row()
        if self.data.index_to_reg[row_idx] == self.data.arch.getip_reg():
            return

        old_expr = getattr(self.data.current_state.regs, self.data.index_to_reg[row_idx])
        new_val = get_int_input("value for %s" %
                                self.data.index_to_reg[row_idx], "Set Reg")
        if new_val is None:
            return
        new_expr = BVV(new_val, old_expr.size)
        setattr(self.data.current_state.regs, self.data.index_to_reg[row_idx], new_expr)
        self.set_reg_value(
            self.data.index_to_reg[row_idx], new_expr, RegisterWidget.dirty_color)

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        return True

    def notifytab(self, newName):
        if newName != self.tabname:
            if self.tabname != "":
                gRegsPerTab[self.tabname] = self.data
                self.stateReset()

            if newName in gRegsPerTab:
                self.data = gRegsPerTab[newName]
                self._init_internal()
        self.tabname = newName

    def contextMenuEvent(self, event):
        self.m_contextMenuManager.show(self.m_menu, self.actionHandler)
