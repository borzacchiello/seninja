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
from PySide2.QtGui import QBrush, QColor
from PySide2.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QWidget,
    QComboBox,
    QTableWidget,
    QTableWidgetItem,
    QMenu,
    QDialog,
    QLineEdit,
    QRadioButton,
    QPushButton
)

from ..utility.expr_wrap_util import symbolic
from ..utility.string_util import (
    constraint_alphanumeric_string,
    constraint_ascii_string
)
from ..expr.bitvector import BVS, BVV


NO_CONSTRAINTS = 0
ASCII_STRING = 1
ALPHANUMERIC_STRING = 2


def get_int(v):
    try:
        return int(v)
    except:
        try:
            return int(v, 16)
        except:
            pass
    return None


class CreateBufferDialog(QDialog):
    constraint_list = {
        NO_CONSTRAINTS: "No constraint",
        ASCII_STRING: "ASCII string",
        ALPHANUMERIC_STRING: "Alphanumeric string"
    }

    def __init__(self, blacklisted_names=[], parent=None):
        super(CreateBufferDialog, self).__init__(parent)

        self.blacklisted_names = blacklisted_names

        layout = QVBoxLayout()

        self.buff_name = QLineEdit("Buffer name")
        self.buff_width = QLineEdit("Buffer size (bytes)")

        layout.addWidget(self.buff_name)
        layout.addWidget(self.buff_width)

        self.constraints = dict()
        for cid in sorted(CreateBufferDialog.constraint_list.keys()):
            name = CreateBufferDialog.constraint_list[cid]
            item = QRadioButton(name)
            if cid == NO_CONSTRAINTS:
                item.setChecked(True)
            self.constraints[cid] = item
            layout.addWidget(item)

        self.ok = QPushButton("Ok")
        self.ok.clicked.connect(self.on_okClick)
        self.cancel = QPushButton("Cancel")
        self.cancel.clicked.connect(self.on_cancelClick)

        layout.addWidget(self.ok)
        layout.addWidget(self.cancel)

        self.setLayout(layout)

        self.res_name = None
        self.res_width = None
        self.res_constraints = None

    def on_okClick(self):
        width = get_int(self.buff_width.text())
        if width is None:
            show_message_box(
                "Error", "Invalid buffer width: must be an integer")
            return
        if self.buff_name.text() in self.blacklisted_names:
            show_message_box(
                "Error", "Name already used")
            return

        self.res_width = width
        self.res_name = self.buff_name.text()

        for cid in self.constraints:
            el = self.constraints[cid]
            if el.isChecked():
                self.res_constraints = cid
                break

        self.accept()

    def on_cancelClick(self):
        self.reject()


def _normalize_tab_name(tab_name):
    return tab_name[:tab_name.find("(")-1]


def _makewidget(parent, val, center=False):
    """ Small helper function that builds a TableWidgetItem and sets up the font the way we want"""
    out = QTableWidgetItem(str(val))
    out.setFlags(Qt.ItemIsEnabled)
    out.setFont(getMonospaceFont(parent))
    if center:
        out.setTextAlignment(Qt.AlignCenter)
    return out


class BufferView(QWidget, DockContextHandler):

    def __init__(self, parent, name, data):
        QWidget.__init__(self, parent)
        DockContextHandler.__init__(self, self, name)

        self.parent = parent
        self.current_state = None
        self.data = data
        self.tab_name = None

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)

        self._layout = QVBoxLayout()

        # Set up register table
        self._table = QTableWidget()
        self._table.setColumnCount(4)
        self._table.setHorizontalHeaderLabels(
            ['Address', 'Name', 'Size', 'Constraints'])
        self._table.horizontalHeader().setStretchLastSection(True)
        self._table.verticalHeader().setVisible(False)

        self._table.setContextMenuPolicy(Qt.CustomContextMenu)
        self._table.customContextMenuRequested.connect(
            self.on_customContextMenuRequested)
        self._table.doubleClicked.connect(self.on_doubleClick)

        self.button = QPushButton("New Buffer")
        self.button.clicked.connect(self.on_newBufferClick)

        self._layout.addWidget(self.button)
        self._layout.addWidget(self._table)

        self.setLayout(self._layout)

    def on_newBufferClick(self):
        if self.current_state is None:
            return

        blacklisted_names = [b[0].name for b in self.current_state.symbolic_buffers]

        new_buff_dialog = CreateBufferDialog(blacklisted_names=blacklisted_names)
        new_buff_dialog.exec_()

        if new_buff_dialog.res_name is None:
            return

        buff = BVS(new_buff_dialog.res_name, new_buff_dialog.res_width * 8)
        address = self.current_state.mem.allocate(new_buff_dialog.res_width)
        if new_buff_dialog.res_constraints == ALPHANUMERIC_STRING:
            constraint_alphanumeric_string(buff, self.current_state)
        elif new_buff_dialog.res_constraints == ASCII_STRING:
            constraint_ascii_string(buff, self.current_state)

        constraint_str = ""
        if new_buff_dialog.res_constraints != NO_CONSTRAINTS:
            constraint_str = CreateBufferDialog.constraint_list[new_buff_dialog.res_constraints]
        self.current_state.mem.store(address, buff)
        self.current_state.symbolic_buffers.append(
            (buff, address, constraint_str)
        )
        self.update(self.current_state)

    def reset(self):
        self.tab_name = None
        self.current_state = None
        self._table.setRowCount(0)
        self.hide()

    def init(self, state):
        self.current_state = state
        self.tab_name = _normalize_tab_name(self.parent.getTabName())
        self.update(state)
        self.show()

    def update(self, state):
        self.current_state = state
        self._table.setRowCount(0)
        self._table.setRowCount(len(self.current_state.symbolic_buffers))
        i = 0
        for buff, address, constraints in self.current_state.symbolic_buffers:
            self._table.setItem(i, 0, _makewidget(self, hex(address)))
            self._table.setItem(i, 1, _makewidget(self, buff.name))
            self._table.setItem(i, 2, _makewidget(self, buff.size // 8))
            self._table.setItem(i, 3, _makewidget(self, constraints))
            i += 1

    # right click menu
    def on_customContextMenuRequested(self, pos):
        item = self._table.itemAt(pos)
        if item is None:
            return
        row_idx = item.row()
        menu = QMenu()
        copy_address = menu.addAction("Copy address")
        eval_as_bytes = menu.addAction("Evaluate as bytes")
        copy_eval = menu.addAction("Copy evaluated bytes")

        action = menu.exec_(self._table.viewport().mapToGlobal(pos))
        if action is None:
            return
        if action == eval_as_bytes:
            buff = self.current_state.symbolic_buffers[row_idx][0]
            res = self.current_state.solver.evaluate(buff).as_bytes()
            show_message_box("%s evaluate" % buff.name, repr(res))
        elif action == copy_address:
            mime = QMimeData()
            mime.setText(hex(self.current_state.symbolic_buffers[row_idx][1]))
            QApplication.clipboard().setMimeData(mime)
        elif action == copy_eval:
            mime = QMimeData()
            buff = self.current_state.symbolic_buffers[row_idx][0]
            res = self.current_state.solver.evaluate(buff).as_bytes()
            mime.setText(repr(res))
            QApplication.clipboard().setMimeData(mime)


    # double click event
    def on_doubleClick(self, item):
        # row_idx = item.row()
        pass

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
            pass

    def contextMenuEvent(self, event):
        self.m_contextMenuManager.show(self.m_menu, self.actionHandler)
