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

gControlPerTab = {}

class ControlView(QWidget):
    def __init__(self, parent):
        QWidget.__init__(self, parent)
        self.parent = parent

        self.toolbar = QToolBar(self, parent)
        self.toolbar.setStyleSheet("""
            QToolButton{"padding: 1x, 1x, 1x"}
        """)

        maxheight = 24

        # ----
        self.toolbar.btnStepInto = QToolButton(self.toolbar)
        self.toolbar.btnStepInto.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnStepInto.setMaximumHeight(maxheight)

        self.toolbar.btnStepInto.actionStep = QAction("", self.toolbar)
        self.toolbar.btnStepInto.actionStep.triggered.connect(lambda: self.perform_step())
        self.toolbar.btnStepInto.actionStep.setIcon(load_icon('stepinto.svg'))

        self.toolbar.btnStepInto.setDefaultAction(self.toolbar.btnStepInto.actionStep)
        self.toolbar.addWidget(self.toolbar.btnStepInto)
        # ----

        # ----
        self.toolbar.btnRunDFS = QToolButton(self.toolbar)
        self.toolbar.btnRunDFS.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnRunDFS.setMaximumHeight(maxheight)

        self.toolbar.btnRunDFS.actionRunDFS = QAction(" DFS", self.toolbar)
        self.toolbar.btnRunDFS.actionRunDFS.triggered.connect(lambda: self.perform_dfs())
        self.toolbar.btnRunDFS.actionRunDFS.setIcon(load_icon('run.svg'))

        self.toolbar.btnRunDFS.setDefaultAction(self.toolbar.btnRunDFS.actionRunDFS)
        self.toolbar.addWidget(self.toolbar.btnRunDFS)
        # ----

        # ----
        self.toolbar.btnRunBFS = QToolButton(self.toolbar)
        self.toolbar.btnRunBFS.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnRunBFS.setMaximumHeight(maxheight)

        self.toolbar.btnRunBFS.actionRunBFS = QAction(" BFS", self.toolbar)
        self.toolbar.btnRunBFS.actionRunBFS.triggered.connect(lambda: self.perform_bfs())
        self.toolbar.btnRunBFS.actionRunBFS.setIcon(load_icon('run.svg'))

        self.toolbar.btnRunBFS.setDefaultAction(self.toolbar.btnRunBFS.actionRunBFS)
        self.toolbar.addWidget(self.toolbar.btnRunBFS)
        # ----

        # ----
        self.toolbar.btnStop = QToolButton(self.toolbar)
        self.toolbar.btnStop.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnStop.setMaximumHeight(maxheight)

        self.toolbar.btnStop.actionStop = QAction("", self.toolbar)
        self.toolbar.btnStop.actionStop.triggered.connect(lambda: self.perform_stop())
        self.toolbar.btnStop.actionStop.setIcon(load_icon('stop.svg'))

        self.toolbar.btnStop.setDefaultAction(self.toolbar.btnStop.actionStop)
        self.toolbar.addWidget(self.toolbar.btnStop)
        # ----

        # ----
        self.toolbar.btnReset = QToolButton(self.toolbar)
        self.toolbar.btnReset.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        self.toolbar.btnReset.setMaximumHeight(maxheight)

        self.toolbar.btnReset.actionReset = QAction("", self.toolbar)
        self.toolbar.btnReset.actionReset.triggered.connect(lambda: self.perform_reset())
        self.toolbar.btnReset.actionReset.setIcon(load_icon('cancel.svg'))

        self.toolbar.btnReset.setDefaultAction(self.toolbar.btnReset.actionReset)
        self.toolbar.addWidget(self.toolbar.btnReset)
        # ----

        self.actionHandler = UIActionHandler()
        self.actionHandler.setupActionHandler(self)

        self.layout = QVBoxLayout()
        self.layout.addWidget(self.toolbar)
        self.setLayout(self.layout)

    def stateInit(self, arch, state):
        pass

    def stateReset(self):
        pass

    def stateUpdate(self, state):
        pass

    def notifytab(self, newName):
        pass

    # def disable(self):
    #     self.toolbar.btnStepInto.setEnabled(False)
    #     self.toolbar.btnRunDFS.setEnabled(False)
    #     self.toolbar.btnRunBFS.setEnabled(False)

    # def enable(self):
    #     self.toolbar.btnStepInto.setEnabled(True)
    #     self.toolbar.btnRunDFS.setEnabled(True)
    #     self.toolbar.btnRunBFS.setEnabled(True)
    #     self.toolbar.btnStop.setEnabled(True)
    #     self.toolbar.btnReset.setEnabled(True)

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

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        return True
