import os

from binaryninjaui import (
    UIActionHandler,
)
from PySide6.QtCore import Qt
from PySide6.QtGui import QPixmap, QIcon, QAction
from PySide6.QtWidgets import (
    QVBoxLayout,
    QWidget,
    QToolBar,
    QToolButton
)

from ..globals import Globals

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
        maxheight = 24

        # ----
        self.toolbar.btnStart = QToolButton(self.toolbar)
        self.toolbar.btnStart.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnStart.setMaximumHeight(maxheight)

        self.toolbar.btnStart.actionStart = QAction("Start...", self.toolbar)
        self.toolbar.btnStart.actionStart.triggered.connect(lambda: self.perform_start())
        self.toolbar.btnStart.actionStart.setIcon(load_icon('start.svg'))

        self.toolbar.btnStart.setDefaultAction(self.toolbar.btnStart.actionStart)
        self.toolbar.addWidget(self.toolbar.btnStart)
        # ----

        # ----
        self.toolbar.btnStepInto = QToolButton(self.toolbar)
        self.toolbar.btnStepInto.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnStepInto.setMaximumHeight(maxheight)

        self.toolbar.btnStepInto.actionStep = QAction("Step", self.toolbar)
        self.toolbar.btnStepInto.actionStep.triggered.connect(lambda: self.perform_step())
        self.toolbar.btnStepInto.actionStep.setIcon(load_icon('stepinto.svg'))

        self.toolbar.btnStepInto.setDefaultAction(self.toolbar.btnStepInto.actionStep)
        self.toolbar.addWidget(self.toolbar.btnStepInto)
        # ----

        # ----
        self.toolbar.btnRunBranch = QToolButton(self.toolbar)
        self.toolbar.btnRunBranch.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnRunBranch.setMaximumHeight(maxheight)

        self.toolbar.btnRunBranch.actionRunUntilBranch = QAction("Run Until Branch", self.toolbar)
        self.toolbar.btnRunBranch.actionRunUntilBranch.triggered.connect(lambda: self.perform_run_until_branch())
        self.toolbar.btnRunBranch.actionRunUntilBranch.setIcon(load_icon('run_branch.svg'))

        self.toolbar.btnRunBranch.setDefaultAction(self.toolbar.btnRunBranch.actionRunUntilBranch)
        self.toolbar.addWidget(self.toolbar.btnRunBranch)
        # ----

        # ----
        self.toolbar.btnRunAddr = QToolButton(self.toolbar)
        self.toolbar.btnRunAddr.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnRunAddr.setMaximumHeight(maxheight)

        self.toolbar.btnRunAddr.actionRunAddr = QAction("Run Until Address", self.toolbar)
        self.toolbar.btnRunAddr.actionRunAddr.triggered.connect(lambda: self.perform_run_until_addr())
        self.toolbar.btnRunAddr.actionRunAddr.setIcon(load_icon('run_addr.svg'))

        self.toolbar.btnRunAddr.setDefaultAction(self.toolbar.btnRunAddr.actionRunAddr)
        self.toolbar.addWidget(self.toolbar.btnRunAddr)
        # ----

        # ----
        self.toolbar.btnRunDFS = QToolButton(self.toolbar)
        self.toolbar.btnRunDFS.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnRunDFS.setMaximumHeight(maxheight)

        self.toolbar.btnRunDFS.actionRunDFS = QAction("Run DFS", self.toolbar)
        self.toolbar.btnRunDFS.actionRunDFS.triggered.connect(lambda: self.perform_dfs())
        self.toolbar.btnRunDFS.actionRunDFS.setIcon(load_icon('run_dfs.svg'))

        self.toolbar.btnRunDFS.setDefaultAction(self.toolbar.btnRunDFS.actionRunDFS)
        self.toolbar.addWidget(self.toolbar.btnRunDFS)
        # ----

        # ----
        self.toolbar.btnRunBFS = QToolButton(self.toolbar)
        self.toolbar.btnRunBFS.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnRunBFS.setMaximumHeight(maxheight)

        self.toolbar.btnRunBFS.actionRunBFS = QAction("Run BFS", self.toolbar)
        self.toolbar.btnRunBFS.actionRunBFS.triggered.connect(lambda: self.perform_bfs())
        self.toolbar.btnRunBFS.actionRunBFS.setIcon(load_icon('run_bfs.svg'))

        self.toolbar.btnRunBFS.setDefaultAction(self.toolbar.btnRunBFS.actionRunBFS)
        self.toolbar.addWidget(self.toolbar.btnRunBFS)
        # ----

        # ----
        self.toolbar.btnStop = QToolButton(self.toolbar)
        self.toolbar.btnStop.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnStop.setMaximumHeight(maxheight)

        self.toolbar.btnStop.actionStop = QAction("Stop", self.toolbar)
        self.toolbar.btnStop.actionStop.triggered.connect(lambda: self.perform_stop())
        self.toolbar.btnStop.actionStop.setIcon(load_icon('stop.svg'))

        self.toolbar.btnStop.setDefaultAction(self.toolbar.btnStop.actionStop)
        self.toolbar.addWidget(self.toolbar.btnStop)
        # ----

        # ----
        self.toolbar.btnReset = QToolButton(self.toolbar)
        self.toolbar.btnReset.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnReset.setMaximumHeight(maxheight)

        self.toolbar.btnReset.actionReset = QAction("Reset", self.toolbar)
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

    def perform_start(self):
        Globals.uimanager.start_se()

    def perform_step(self):
        Globals.uimanager.async_step()

    def perform_dfs(self):
        Globals.uimanager.async_run_dfs_searcher()

    def perform_bfs(self):
        Globals.uimanager.async_run_bfs_searcher()

    def perform_run_until_branch(self):
        Globals.uimanager.async_continue_until_branch()

    def perform_run_until_addr(self):
        Globals.uimanager.async_continue_until_address(Globals.uimanager.bv.file.offset)

    def perform_stop(self):
        if Globals.uimanager.running:
            Globals.uimanager.stop = True

    def perform_reset(self):
        Globals.uimanager.async_reset_se()

    def notifyOffsetChanged(self, offset):
        pass

    def shouldBeVisible(self, view_frame):
        if view_frame is None:
            return False
        return True
