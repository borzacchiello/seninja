from binaryninjaui import (
    getMonospaceFont,
    getThemeColor,
    ThemeColor
)
from PySide6.QtCore import Qt
from PySide6.QtGui import QBrush
from PySide6.QtWidgets import (
    QVBoxLayout,
    QWidget,
    QTableWidget,
    QTableWidgetItem,
)

from ..globals import Globals

gStatesPerTab = {}

def _makewidget(parent, val, center=False):
    out = QTableWidgetItem(str(val))
    out.setFlags(Qt.ItemIsEnabled)
    out.setFont(getMonospaceFont(parent))
    if center:
        out.setTextAlignment(Qt.AlignCenter)
    return out

class StateViewData(object):
    def __init__(self):
        self.current_state = None
        self.index_to_state_address = dict()
        self.state_collection = []
        self.active_idx = None

class StateView(QWidget):
    def __init__(self, parent):
        QWidget.__init__(self, parent)

        self.parent = parent
        self.tabname = ""
        self.data = StateViewData()

        # Set up register table
        self.table = QTableWidget()
        self.table.setColumnCount(2)
        self.table.setHorizontalHeaderLabels(['Status', 'State'])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)

        self.active_state_color = QBrush(getThemeColor(ThemeColor.GreenStandardHighlightColor))
        self.defered_state_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
        self.unsat_state_color = QBrush(getThemeColor(ThemeColor.OrangeStandardHighlightColor))
        self.error_state_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
        self.avoided_state_color = QBrush(getThemeColor(ThemeColor.MagentaStandardHighlightColor))
        self.exited_state_color = QBrush(getThemeColor(ThemeColor.BlackStandardHighlightColor))
        self.item_color = QBrush(getThemeColor(ThemeColor.BlackStandardHighlightColor))
        self.item_color_inverted = QBrush(getThemeColor(ThemeColor.WhiteStandardHighlightColor))

        self.table.doubleClicked.connect(self.on_doubleClick)

        self.layout = QVBoxLayout()
        self.layout.addWidget(self.table)
        self.setLayout(self.layout)

    def stateReset(self):
        self.data = StateViewData()
        self.table.setRowCount(0)

    def _init_internal(self):
        self.set_state_table(self.data.current_state)

    def stateInit(self, arch, state):
        self.stateUpdate(state)

    def stateUpdate(self, state):
        self.data.current_state = state
        self._init_internal()

    def set_state_table(self, state):
        STATE_ACTIVE = 0
        STATE_DEFERRED = 1
        STATE_UNSAT = 2
        STATE_ERROR = 3
        STATE_AVOIDED = 4
        STATE_EXITED = 5
        self.data.state_collection.clear()
        
        deferred_states = Globals.uimanager.executor.fringe.deferred
        unsat_states = Globals.uimanager.executor.fringe.get_unsat_states
        error_states = Globals.uimanager.executor.fringe.get_error_states
        avoided_states = Globals.uimanager.executor.fringe.get_avoided_states
        exited_states = Globals.uimanager.executor.fringe.get_exited_states

        rowCount = len(deferred_states)+len(unsat_states)+len(error_states)+len(avoided_states)+len(exited_states)
        if state:
            rowCount += 1
        self.table.setRowCount(rowCount)
        if state:
            self.data.state_collection.append((state,STATE_ACTIVE))

        for idx, a in enumerate(deferred_states):
            self.data.state_collection.append((a,STATE_DEFERRED))
        for idx, a in enumerate(unsat_states):
            self.data.state_collection.append((a,STATE_UNSAT))
        for idx, a in enumerate(error_states):
            self.data.state_collection.append((a[1],STATE_ERROR))
        for idx, a in enumerate(avoided_states):
            self.data.state_collection.append((a,STATE_AVOIDED))
        for idx, a in enumerate(exited_states):
            self.data.state_collection.append((a,STATE_EXITED))
        
        self.data.state_collection = sorted(self.data.state_collection, key=lambda t: t[0].get_ip())

        for idx, (a,s) in enumerate(self.data.state_collection):
            if s==STATE_DEFERRED:
                state_colour = self.defered_state_color
                state_text_colour = self.item_color
                state_status = "Deferred"
            if s==STATE_ACTIVE:
                state_colour = self.active_state_color
                state_text_colour = self.item_color
                state_status = "Active"
                self.data.active_idx = idx
            if s==STATE_UNSAT:
                state_colour = self.unsat_state_color
                state_text_colour = self.item_color
                state_status = "UnSat"
            if s==STATE_ERROR:
                state_colour = self.error_state_color
                state_text_colour = self.item_color
                state_status = "Errored"
            if s==STATE_AVOIDED:
                state_colour = self.avoided_state_color
                state_text_colour = self.item_color
                state_status = "Avoided"
            if s==STATE_EXITED:
                state_colour = self.exited_state_color
                state_text_colour = self.item_color_inverted
                state_status = "Exited"

            self.table.setItem(idx, 0, _makewidget(self, state_status))
            self.table.setItem(idx, 1, _makewidget(self, f"State_{hex(a.get_ip())}"))
            self.table.item(idx, 0).setBackground(state_colour)
            self.table.item(idx, 1).setBackground(state_colour)
            self.table.item(idx, 0).setForeground(state_text_colour)
            self.table.item(idx, 1).setForeground(state_text_colour)
            self.data.index_to_state_address[idx] = a.get_ip()    

    # double click event
    def on_doubleClick(self, item):
        row_idx = item.row()
        if row_idx == self.data.active_idx:
            return
        state_addr = self.data.index_to_state_address[row_idx]
        Globals.uimanager.async_change_current_state(state_addr)

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        return True

    def notifytab(self, newName):
        if newName != self.tabname:
            if self.tabname != "":
                gStatesPerTab[self.tabname] = self.data
                self.stateReset()

            if newName in gStatesPerTab:
                self.data = gStatesPerTab[newName]
                self._init_internal()
        self.tabname = newName
