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
        self.toolbar.setStyleSheet("QToolBar{spacing:0px;}")
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
        self.toolbar.btnSetTarget = QToolButton(self.toolbar)
        self.toolbar.btnSetTarget.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnSetTarget.setMaximumHeight(maxheight)

        self.toolbar.btnSetTarget.actionSetTarget = QAction("Set Target", self.toolbar)
        self.toolbar.btnSetTarget.actionSetTarget.triggered.connect(lambda: self.set_target())
        self.toolbar.btnSetTarget.actionSetTarget.setIcon(load_icon('set_target.svg'))

        self.toolbar.btnSetTarget.setDefaultAction(self.toolbar.btnSetTarget.actionSetTarget)
        self.toolbar.addWidget(self.toolbar.btnSetTarget)
        # ----

        # ----
        self.toolbar.btnSetAvoid = QToolButton(self.toolbar)
        self.toolbar.btnSetAvoid.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnSetAvoid.setMaximumHeight(maxheight)

        self.toolbar.btnSetAvoid.actionSetAvoid = QAction("Set Avoid", self.toolbar)
        self.toolbar.btnSetAvoid.actionSetAvoid.triggered.connect(lambda: self.set_avoid())
        self.toolbar.btnSetAvoid.actionSetAvoid.setIcon(load_icon('set_avoid.svg'))

        self.toolbar.btnSetAvoid.setDefaultAction(self.toolbar.btnSetAvoid.actionSetAvoid)
        self.toolbar.addWidget(self.toolbar.btnSetAvoid)
        # ----

        # ----
        self.toolbar.btnResetSearcher = QToolButton(self.toolbar)
        self.toolbar.btnResetSearcher.setToolButtonStyle(Qt.ToolButtonIconOnly)
        self.toolbar.btnResetSearcher.setMaximumHeight(maxheight)

        self.toolbar.btnResetSearcher.actionResetSearcher = QAction("Reset Searchers", self.toolbar)
        self.toolbar.btnResetSearcher.actionResetSearcher.triggered.connect(lambda: self.reset_searchers())
        self.toolbar.btnResetSearcher.actionResetSearcher.setIcon(load_icon('reset_searchers.svg'))

        self.toolbar.btnResetSearcher.setDefaultAction(self.toolbar.btnResetSearcher.actionResetSearcher)
        self.toolbar.addWidget(self.toolbar.btnResetSearcher)
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

    def set_target(self):
        Globals.uimanager.set_run_target(Globals.uimanager.bv.file.offset)

    def set_avoid(self):
        Globals.uimanager.set_run_avoid(Globals.uimanager.bv.file.offset)

    def reset_searchers(self):
        Globals.uimanager.reset_searchers()

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
