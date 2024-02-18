from binaryninjaui import (
    SidebarWidget,
    SidebarWidgetType,
    SidebarWidgetLocation,
    SidebarContextSensitivity,
    getThemeColor,
    ThemeColor
)
from PySide6 import QtCore
from PySide6.QtGui import (
    QPainter,
    QPixmap,
    QBrush,
    QImage,
    QIcon
)
from PySide6.QtSvg import QSvgRenderer
from PySide6.QtWidgets import (
    QVBoxLayout,
    QTabWidget
)

from .files_view import FilesView
from .registers_view import RegisterWidget
from .control_view import ControlView
from .state_view import StateView
from .buffer_view import BufferView
from .memory_view import MemoryView

import os

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

class SENinjaWidget(SidebarWidget):
    updateStateSignal = QtCore.Signal(object)
    initSignal        = QtCore.Signal(object, object)
    resetSignal       = QtCore.Signal()

    dirty_color      = QBrush(getThemeColor(ThemeColor.OrangeStandardHighlightColor))
    expression_color = QBrush(getThemeColor(ThemeColor.RedStandardHighlightColor))
    symbolic_color   = QBrush(getThemeColor(ThemeColor.BlueStandardHighlightColor))
    no_color         = QBrush(getThemeColor(ThemeColor.WhiteStandardHighlightColor))

    def __init__(self, name, frame, data):
        SidebarWidget.__init__(self, name)
        self.updateStateSignal.connect(self.stateUpdate)
        self.initSignal.connect(self.stateInit)
        self.resetSignal.connect(self.stateReset)

        self.tabs = QTabWidget(frame)
        self.regs = RegisterWidget(frame)
        self.controls = ControlView(frame)
        self.states = StateView(frame)
        self.buffers = BufferView(frame)
        self.files = FilesView(frame)
        self.mem = MemoryView(frame)

        self.tabs.addTab(self.regs, "Registers")
        self.tabs.addTab(self.mem, "Memory")
        self.tabs.addTab(self.states, "States")
        self.tabs.addTab(self.buffers, "Buffers")
        self.tabs.addTab(self.files, "Files")

        self.layout = QVBoxLayout()
        self.layout.addWidget(self.controls)
        self.layout.addWidget(self.tabs)
        self.layout.setSpacing(0)
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.setLayout(self.layout)

    def stateUpdate(self, state):
        self.regs.stateUpdate(state)
        self.states.stateUpdate(state)
        self.buffers.stateUpdate(state)
        self.controls.stateUpdate(state)
        self.files.stateUpdate(state)
        self.mem.stateUpdate(state)

    def stateInit(self, arch, state):
        self.regs.stateInit(arch, state)
        self.states.stateInit(arch, state)
        self.buffers.stateInit(arch, state)
        self.controls.stateInit(arch, state)
        self.files.stateInit(arch, state)
        self.mem.stateInit(arch, state)

    def stateReset(self):
        self.regs.stateReset()
        self.states.stateReset()
        self.buffers.stateReset()
        self.controls.stateReset()
        self.files.stateReset()
        self.mem.stateReset()

    def notifyViewChanged(self, view_frame):
        newName = view_frame.getTabName() if view_frame is not None else ""
        self.regs.notifytab(newName)
        self.states.notifytab(newName)
        self.buffers.notifytab(newName)
        self.controls.notifytab(newName)
        self.files.notifytab(newName)
        self.mem.notifytab(newName)

    def disableAll(self):
        self.regs.setDisabled(True)
        self.states.setDisabled(True)
        self.buffers.setDisabled(True)
        self.files.setDisabled(True)
        self.mem.setDisabled(True)

    def enableAll(self):
        self.regs.setEnabled(True)
        self.states.setEnabled(True)
        self.buffers.setEnabled(True)
        self.files.setEnabled(True)
        self.mem.setEnabled(True)

class SENinjaWidgetType(SidebarWidgetType):
    name = "SENinja"

    def __init__(self):
        path_this_file = os.path.abspath(__file__)
        path_this_dir = os.path.dirname(path_this_file)
        path_icons = os.path.join(path_this_dir, '..', 'media', 'icons')
        path_icon = os.path.join(path_icons, "pi.svg")

        renderer = QSvgRenderer(path_icon)
        icon = QImage(56, 56, QImage.Format_ARGB32)
        icon.fill(0xaaA08080)

        p = QPainter(icon)
        renderer.render(p)
        p.end()
        SidebarWidgetType.__init__(self, icon, SENinjaWidgetType.name)

    def createWidget(self, frame, data):
        # This callback is called when a widget needs to be created for a given context. Different
        # widgets are created for each unique BinaryView. They are created on demand when the sidebar
        # widget is visible and the BinaryView becomes active.
        return SENinjaWidget(SENinjaWidgetType.name, frame, data)

    def defaultLocation(self):
        # Default location in the sidebar where this widget will appear
        return SidebarWidgetLocation.LeftContent

    def contextSensitivity(self):
        # Context sensitivity controls which contexts have separate instances of the sidebar widget.
        # Using `contextSensitivity` instead of the deprecated `viewSensitive` callback allows sidebar
        # widget implementations to reduce resource usage.

        # This example widget uses a single instance and detects view changes.
        return SidebarContextSensitivity.SelfManagedSidebarContext
