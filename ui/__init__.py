from ..seninja_globals import globs
from PySide6.QtWidgets import QApplication
from binaryninjaui import DockHandler, UIAction, UIActionHandler, Menu, GlobalArea
from PySide6.QtCore import Qt
from .registers_view import RegisterView
from .state_view import StateView
from .control_view import ControlView
from .memory_view import MemoryView
from .buffer_view import BufferView
from .argv_form import GetArgvDialog

class BNWidgets(object):
    RW = None
    MW = None
    BW = None
    CW = None
    SW = None


def _get_registerview_widget(name, parent, data):
    BNWidgets.RW = RegisterView(parent, name, data)
    BNWidgets.RW.setEnabled(False)
    return BNWidgets.RW

def _get_controlview_widget(name, parent, data):
    BNWidgets.CW = ControlView(parent, name, data)
    BNWidgets.CW.disable()
    return BNWidgets.CW

def _get_memoryview_widget(name, data):
    BNWidgets.MW = MemoryView(name, data, BNWidgets)
    BNWidgets.MW.setEnabled(False)
    return BNWidgets.MW


def _get_buffer_view_widget(name, parent, data):
    BNWidgets.BW = BufferView(parent, name, data)
    BNWidgets.BW.setEnabled(False)
    return BNWidgets.BW

def _get_state_view_widget(name, parent, data):
    BNWidgets.SW = StateView(parent, name, data)
    BNWidgets.SW.setEnabled(False)
    return BNWidgets.SW


def _launchArgvDialog(context):
    if globs.executor is None:
        return
    d = GetArgvDialog(globs.executor.state)
    d.exec_()
    ui_sync_view(globs.executor.state, True)


def _registerDynamicWidgets():
    dock_handler = DockHandler.getActiveDockHandler()
    dock_handler.addDockWidget(
        "SENinja Controls",
        _get_controlview_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )
    dock_handler.addDockWidget(
        "SENinja State View",
        _get_state_view_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )
    dock_handler.addDockWidget(
        "SENinja Registers",
        _get_registerview_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )
    dock_handler.addDockWidget(
        "SENinja Buffers",
        _get_buffer_view_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )
    GlobalArea.addWidget(lambda context: _get_memoryview_widget("SENinja Memory", {}))

def _registerUIActions():
    UIAction.registerAction("SENinja\\Setup argv...")
    UIActionHandler.globalActions().bindAction(
        "SENinja\\Setup argv...", UIAction(_launchArgvDialog))
    Menu.mainMenu("Tools").addAction("SENinja\\Setup argv...", "Setup argv...")


def enable_widgets():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None
    assert BNWidgets.CW is not None
    assert BNWidgets.SW is not None

    BNWidgets.RW.setEnabled(True)
    BNWidgets.MW.setEnabled(True)
    BNWidgets.BW.setEnabled(True)
    BNWidgets.CW.enable()
    BNWidgets.SW.setEnabled(True)


def disable_widgets():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None
    assert BNWidgets.CW is not None
    assert BNWidgets.SW is not None

    # Refresh state table
    BNWidgets.SW.set_state_table(None)

    BNWidgets.RW.setEnabled(False)
    BNWidgets.MW.setEnabled(False)
    BNWidgets.BW.setEnabled(False)
    BNWidgets.CW.disable()
    BNWidgets.SW.setEnabled(False)


def ui_set_arch(arch, state):
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None
    assert BNWidgets.CW is not None
    assert BNWidgets.SW is not None

    BNWidgets.RW.init(arch, state)
    BNWidgets.MW.init(arch, state)
    BNWidgets.BW.init(state)
    BNWidgets.SW.init(state)
    BNWidgets.CW.init()

    dock_handler = DockHandler.getActiveDockHandler()
    dock_handler.setVisible("SENinja Registers", True)
    dock_handler.setVisible("SENinja Buffers", True)
    dock_handler.setVisible("SENinja Controls", True)
    dock_handler.setVisible("SENinja State View", True)


def ui_sync_view(state, delta=True):
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None
    assert BNWidgets.CW is not None
    assert BNWidgets.SW is not None

    if BNWidgets.RW.isVisible():
        BNWidgets.RW.set_reg_values(state)
    if BNWidgets.MW.isVisible():
        if delta:
            BNWidgets.MW.update_mem_delta(state)
        else:
            BNWidgets.MW.update_mem(state)
    if BNWidgets.BW.isVisible():
        BNWidgets.BW.update_state(state)
    if BNWidgets.SW.isVisible():
        BNWidgets.SW.update_state(state)

def ui_reset_view():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None
    assert BNWidgets.CW is not None
    assert BNWidgets.SW is not None

    BNWidgets.RW.reset()
    BNWidgets.MW.reset()
    BNWidgets.BW.reset()
    BNWidgets.CW.reset()
    BNWidgets.SW.reset()

    dock_handler = DockHandler.getActiveDockHandler()
    dock_handler.setVisible("SENinja Registers", False)
    dock_handler.setVisible("SENinja Buffers", False)
    dock_handler.setVisible("SENinja Controls", False)
    dock_handler.setVisible("SENinja State View", False)


_registerDynamicWidgets()
_registerUIActions()
