from ..seninja_globals import globs

from binaryninjaui import (
    DockContextHandler,
    getMonospaceFont,
    getThemeColor,
    ThemeColor
)
from PySide6 import QtCore
from PySide6.QtCore import Qt
from PySide6.QtGui import QBrush
from PySide6.QtWidgets import (
    QVBoxLayout,
    QWidget,
    QTableWidget,
    QTableWidgetItem,
    QMenu
)

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


class StateView(QWidget, DockContextHandler):
    updateStateSignal = QtCore.Signal(object)

    def __init__(self, parent, name, data):
        QWidget.__init__(self, parent)
        DockContextHandler.__init__(self, self, name)
        self.updateStateSignal.connect(self.update_state)

        self.parent = parent
        self.tab_name = None
        self.data = data
        self.index_to_state_address = dict()
        self.state_collection = []

       # Set up register table
        self._table = QTableWidget()
        self._table.setColumnCount(2)
        self._table.setHorizontalHeaderLabels(['Status', 'State'])
        self._table.horizontalHeader().setStretchLastSection(True)
        self._table.verticalHeader().setVisible(False)

        self.active_state_color = QBrush(getThemeColor(ThemeColor.GreenStandardHighlightColor))
        self.defered_state_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
        self.unsat_state_color = QBrush(getThemeColor(ThemeColor.OrangeStandardHighlightColor))
        self.error_state_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
        self.avoided_state_color = QBrush(getThemeColor(ThemeColor.MagentaStandardHighlightColor))
        self.exited_state_color = QBrush(getThemeColor(ThemeColor.BlackStandardHighlightColor))
        self.item_color = QBrush(getThemeColor(ThemeColor.BlackStandardHighlightColor))
        self.item_color_inverted = QBrush(getThemeColor(ThemeColor.WhiteStandardHighlightColor))

        self._table.doubleClicked.connect(self.on_doubleClick)

        self._layout = QVBoxLayout()
        self._layout.addWidget(self._table)
        self.setLayout(self._layout)

    def reset(self):
        self.tab_name = None
        self.arch = None
        self.index_to_state_address = dict()
        self.state_collection = []
        self.symb_idx = 0
        self.active_idx = None
        self._table.setRowCount(0)

    def init(self, state):
        try:
            self.tab_name = _normalize_tab_name(self.parent.getTabName())
        except RuntimeError:
            self.reset()
            return
        self.set_state_table(state)

    def update_state(self, state):
        self.set_state_table(state)

    def set_state_table(self, state):
        STATE_ACTIVE = 0
        STATE_DEFERRED = 1
        STATE_UNSAT = 2
        STATE_ERROR = 3
        STATE_AVOIDED = 4
        STATE_EXITED = 5
        self.state_collection.clear()
        
        deferred_states = globs.executor.fringe.deferred
        unsat_states = globs.executor.fringe.get_unsat_states
        error_states = globs.executor.fringe.get_error_states
        avoided_states = globs.executor.fringe.get_avoided_states
        exited_states = globs.executor.fringe.get_exited_states

        rowCount = len(deferred_states)+len(unsat_states)+len(error_states)+len(avoided_states)+len(exited_states)
        if state:
            rowCount += 1
        self._table.setRowCount(rowCount)
        if state:
            self.state_collection.append((state,STATE_ACTIVE))

        for idx, a in enumerate(deferred_states):
            self.state_collection.append((a,STATE_DEFERRED))
        for idx, a in enumerate(unsat_states):
            self.state_collection.append((a,STATE_UNSAT))
        for idx, a in enumerate(error_states):
            self.state_collection.append((a[1],STATE_ERROR))
        for idx, a in enumerate(avoided_states):
            self.state_collection.append((a,STATE_AVOIDED))
        for idx, a in enumerate(exited_states):
            self.state_collection.append((a,STATE_EXITED))
        
        self.state_collection = sorted(self.state_collection, key=lambda t: t[0].get_ip())

        for idx, (a,s) in enumerate(self.state_collection):
            if s==STATE_DEFERRED:
                state_colour = self.defered_state_color
                state_text_colour = self.item_color
                state_status = "Deferred"
            if s==STATE_ACTIVE:
                state_colour = self.active_state_color
                state_text_colour = self.item_color
                state_status = "Active"
                self.active_idx = idx
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


            self._table.setItem(idx, 0, _makewidget(self, state_status))
            self._table.setItem(idx, 1, _makewidget(self, f"State_{hex(a.get_ip())}"))
            self._table.item(idx, 0).setBackground(state_colour)
            self._table.item(idx, 1).setBackground(state_colour)
            self._table.item(idx, 0).setForeground(state_text_colour)
            self._table.item(idx, 1).setForeground(state_text_colour)
            self.index_to_state_address[idx] = a.get_ip()    



    # double click event
    def on_doubleClick(self, item):
        row_idx = item.row()
        if row_idx == self.active_idx:
            return
        state_addr = self.index_to_state_address[row_idx]
        globs.actions_change_state(globs.bv, state_addr)

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

