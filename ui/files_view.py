from binaryninja import BackgroundTaskThread
from binaryninja.interaction import (
    show_message_box,
    get_int_input,
)
from binaryninjaui import (
    getMonospaceFont,
    UIActionHandler
)
from PySide6.QtCore import Qt, QMimeData
from PySide6.QtWidgets import (
    QApplication,
    QVBoxLayout,
    QWidget,
    QTableWidget,
    QTableWidgetItem,
    QMenu,
)
from ..expr.bitvector import BVS, BVV

NO_CONSTRAINTS = 0
ASCII_STRING = 1
ALPHANUMERIC_STRING = 2

gFilesPerTab = {}

def _makewidget(parent, val, center=False):
    """ Small helper function that builds a TableWidgetItem and sets up the font the way we want"""
    out = QTableWidgetItem(str(val))
    out.setFlags(Qt.ItemIsEnabled)
    out.setFont(getMonospaceFont(parent))
    if center:
        out.setTextAlignment(Qt.AlignCenter)
    return out

class FilesViewBT(BackgroundTaskThread):
    def __init__(self, msg, bw, callback, pars):
        BackgroundTaskThread.__init__(self, msg, False)
        self.bw = bw
        self.pars = pars
        self.callback = callback

    def run(self):
        self.callback(*self.pars)

class FilesViewData(object):
    def __init__(self):
        self.current_state = None

class FilesView(QWidget):
    def __init__(self, parent):
        QWidget.__init__(self, parent)

        self.parent = parent
        self.data = FilesViewData()
        self.tabname = ""

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)

        self.layout = QVBoxLayout()

        self.table = QTableWidget()
        self.table.setColumnCount(2)
        self.table.setHorizontalHeaderLabels(
            ['Path', 'Size'])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)

        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(
            self.on_customContextMenuRequested)
        self.table.doubleClicked.connect(self.on_doubleClick)

        self.layout.addWidget(self.table)
        self.setLayout(self.layout)

    def stateReset(self):
        self.data.current_state = None
        self.table.setRowCount(0)

    def _init_internal(self):
        self.stateUpdate(self.data.current_state)

    def stateInit(self, arch, state):
        self.data.current_state = state
        self._init_internal()

    def stateUpdate(self, state):
        self.data.current_state = state
        self.table.setRowCount(0)
        if state is None:
            return

        self.table.setRowCount(len(state.os.filesystem))
        for i, path in enumerate(sorted(state.os.filesystem.keys())):
            self.table.setItem(i, 0, _makewidget(self, path))
            self.table.setItem(i, 1, _makewidget(self, state.os.filesystem[path].file_size))

    # right click menu
    def on_customContextMenuRequested(self, pos):
        item = self.table.itemAt(pos)
        if item is None:
            return
        row_idx = item.row()
        menu = QMenu()

        a = menu.addAction("Evaluate upto")
        a.triggered.connect(lambda: self._menuAction_evaluate_upto_buffer(row_idx))
        a = menu.addAction("Evaluate as bytes")
        a.triggered.connect(lambda: self._menuAction_evaluate_buffer(row_idx))
        a = menu.addAction("Evaluate as string")
        a.triggered.connect(lambda: self._menuAction_evaluate_buffer(row_idx, as_string=True))
        a = menu.addAction("Copy evaluated bytes")
        a.triggered.connect(lambda: self._menuAction_copy_evaluated_buffer(row_idx))
        menu.exec_(self.table.viewport().mapToGlobal(pos))

    def _menuAction_evaluate_buffer(self, files_id, as_string=False):
        files = sorted(self.data.current_state.os.filesystem.keys())
        symfile = self.data.current_state.os.filesystem[files[files_id]]
        if symfile.file_size == 0:
            return
        data = symfile.data.load(BVV(0, symfile.data.bits), symfile.file_size)
        dataBytes = self.data.current_state.solver.evaluate(data).as_bytes()

        if not as_string:
            res = dataBytes
            res = repr(res)[2:-1]
        else:
            res = ""
            for el in dataBytes:
                if el == 0:
                    break
                res += chr(el) if el >= 32 and el <= 126 else "."
        show_message_box("evaluate", res)

    def _menuAction_evaluate_upto_buffer(self, files_id):
        files = sorted(self.data.current_state.os.filesystem.keys())
        symfile = self.data.current_state.os.filesystem[files[files_id]]
        if symfile.file_size == 0:
            return
        data = symfile.data.load(BVV(0, symfile.data.bits), symfile.file_size)

        n_eval = get_int_input("How many values (upto) ?", "Number of distinct values")
        if n_eval is None:
            return
        r = ""
        for i, v in enumerate(self.data.current_state.solver.evaluate_upto(data, n_eval)):
            r += "solution %d: %s\n" % (i, hex(v.value))

        show_message_box("evaluate", r)

    def _menuAction_copy_evaluated_buffer(self, files_id):
        files = sorted(self.data.current_state.os.filesystem.keys())
        symfile = self.data.current_state.os.filesystem[files[files_id]]
        if symfile.file_size == 0:
            return
        data = symfile.data.load(BVV(0, symfile.data.bits), symfile.file_size)

        mime = QMimeData()
        res = self.data.current_state.solver.evaluate(data).as_bytes()
        res = '"' + repr(res)[2:-1] + '"'
        mime.setText(res)
        QApplication.clipboard().setMimeData(mime)

    # double click event
    def on_doubleClick(self, item):
        pass

    def contextMenuEvent(self, event):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        return True

    def notifytab(self, newName):
        if newName != self.tabname:
            if self.tabname != "":
                gFilesPerTab[self.tabname] = self.data
                self.stateReset()

            if newName in gFilesPerTab:
                self.data = gFilesPerTab[newName]
                self._init_internal()
        self.tabname = newName
