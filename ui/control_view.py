import os
from ..seninja_globals import globs

from binaryninjaui import (
    DockContextHandler,
    UIActionHandler,
    getThemeColor,
    ThemeColor
)
from PySide6.QtCore import Qt
from PySide6.QtGui import QBrush, QPixmap, QIcon, QAction
from PySide6.QtWidgets import (
    QVBoxLayout,
    QWidget,
    QToolBar,
    QToolButton
)

def _normalize_tab_name(tab_name):
    return tab_name[:tab_name.find("(")-1]

def load_icon(fname_icon):
    path_this_file = os.path.abspath(__file__)
    path_this_dir = os.path.dirname(path_this_file)
    path_icons = os.path.join(path_this_dir, '..', 'media', 'icons')
    path_icon = os.path.join(path_icons, fname_icon)

    pixmap = QPixmap(path_icon)

    icon = QIcon()
    icon.addPixmap(pixmap, QIcon.Normal)
    icon.addPixmap(pixmap, QIcon.Disabled)

    return icon

class ControlView(QWidget, DockContextHandler):

    dirty_color = QBrush(getThemeColor(ThemeColor.OrangeStandardHighlightColor))
    expression_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
    symbolic_color = QBrush(getThemeColor(ThemeColor.BlueStandardHighlightColor))
    no_color = QBrush(getThemeColor(ThemeColor.WhiteStandardHighlightColor))

    def __init__(self, parent, name, data):
        QWidget.__init__(self, parent)
        DockContextHandler.__init__(self, self, name)

        self.parent = parent
        self.tab_name = None
        self.data = data

        self.toolbar = QToolBar(self, parent)
        self.toolbar.setStyleSheet("""
                QToolButton{"padding: 1x, 1x, 1x"}
                """)


        # ----
        self.toolbar.btnStepInto = QToolButton(self.toolbar)
        self.toolbar.btnStepInto.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnStepInto.setMaximumHeight(24)

        self.toolbar.btnStepInto.actionStep = QAction(". Step", self.toolbar)
        self.toolbar.btnStepInto.actionStep.triggered.connect(lambda: self.perform_step())
        self.toolbar.btnStepInto.actionStep.setIcon(load_icon('stepinto.svg'))

        self.toolbar.btnStepInto.setDefaultAction(self.toolbar.btnStepInto.actionStep)
        self.toolbar.addWidget(self.toolbar.btnStepInto)
        # ----

        # ----
        self.toolbar.btnRunDFS = QToolButton(self.toolbar)
        self.toolbar.btnRunDFS.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnRunDFS.setMaximumHeight(24)

        self.toolbar.btnRunDFS.actionRunDFS = QAction(". DFS", self.toolbar)
        self.toolbar.btnRunDFS.actionRunDFS.triggered.connect(lambda: self.perform_dfs())
        self.toolbar.btnRunDFS.actionRunDFS.setIcon(load_icon('run.svg'))

        self.toolbar.btnRunDFS.setDefaultAction(self.toolbar.btnRunDFS.actionRunDFS)
        self.toolbar.addWidget(self.toolbar.btnRunDFS)
        # ----

        # ----
        self.toolbar.btnRunBFS = QToolButton(self.toolbar)
        self.toolbar.btnRunBFS.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnRunBFS.setMaximumHeight(24)

        self.toolbar.btnRunBFS.actionRunBFS = QAction(". BFS", self.toolbar)
        self.toolbar.btnRunBFS.actionRunBFS.triggered.connect(lambda: self.perform_bfs())
        self.toolbar.btnRunBFS.actionRunBFS.setIcon(load_icon('run.svg'))

        self.toolbar.btnRunBFS.setDefaultAction(self.toolbar.btnRunBFS.actionRunBFS)
        self.toolbar.addWidget(self.toolbar.btnRunBFS)
        # ----

        # ----
        self.toolbar.btnStop = QToolButton(self.toolbar)
        self.toolbar.btnStop.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnStop.setMaximumHeight(24)

        self.toolbar.btnStop.actionStop = QAction(". Stop", self.toolbar)
        self.toolbar.btnStop.actionStop.triggered.connect(lambda: self.perform_stop())
        self.toolbar.btnStop.actionStop.setIcon(load_icon('stop.svg'))

        self.toolbar.btnStop.setDefaultAction(self.toolbar.btnStop.actionStop)
        self.toolbar.addWidget(self.toolbar.btnStop)
        # ----

        # ----
        self.toolbar.btnReset = QToolButton(self.toolbar)
        self.toolbar.btnReset.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnReset.setMaximumHeight(24)

        self.toolbar.btnReset.actionReset = QAction(". Exit", self.toolbar)
        self.toolbar.btnReset.actionReset.triggered.connect(lambda: self.perform_reset())
        self.toolbar.btnReset.actionReset.setIcon(load_icon('cancel.svg'))

        self.toolbar.btnReset.setDefaultAction(self.toolbar.btnReset.actionReset)
        self.toolbar.addWidget(self.toolbar.btnReset)
        # ----

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)


        self._layout = QVBoxLayout()
        self._layout.addWidget(self.toolbar)
        self.setLayout(self._layout)

    
    def init(self):
        self.tab_name = _normalize_tab_name(self.parent.getTabName())
        
    def disable(self):
        self.toolbar.btnStepInto.setEnabled(False)
        self.toolbar.btnRunDFS.setEnabled(False)
        self.toolbar.btnRunBFS.setEnabled(False)

    def enable(self):
        self.toolbar.btnStepInto.setEnabled(True)
        self.toolbar.btnRunDFS.setEnabled(True)
        self.toolbar.btnRunBFS.setEnabled(True)
        self.toolbar.btnStop.setEnabled(True)
        self.toolbar.btnReset.setEnabled(True)

    def perform_step(self):
        globs.actions_step(globs.bv)

    def perform_dfs(self):
        globs.actions_dfs(globs.bv)

    def perform_bfs(self):
        globs.actions_bfs(globs.bv)

    def perform_stop(self):
        if globs._running:  # race conditions
            globs._stop = True

    def perform_reset(self):
        globs.actions_reset(globs.bv, globs.started_address)

    def reset(self):
        self.tab_name = None
        self.current_state = None

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

