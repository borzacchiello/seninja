from ..seninja_globals import globs
from PySide2.QtWidgets import QApplication
from binaryninjaui import DockHandler, UIAction, UIActionHandler, Menu
from PySide2.QtCore import Qt
from .registers_view import RegisterView
from .memory_view import MemoryView
from .buffer_view import BufferView
from .argv_form import GetArgvDialog

class BNWidgets(object):
    RW = None
    MW = None
    BW = None


def _get_registerview_widget(name, parent, data):
    BNWidgets.RW = RegisterView(parent, name, data)
    BNWidgets.RW.setEnabled(False)
    return BNWidgets.RW


def _get_memoryview_widget(name, parent, data):
    BNWidgets.MW = MemoryView(parent, name, data, BNWidgets)
    BNWidgets.MW.setEnabled(False)
    return BNWidgets.MW


def _get_buffer_view_widget(name, parent, data):
    BNWidgets.BW = BufferView(parent, name, data)
    BNWidgets.BW.setEnabled(False)
    return BNWidgets.BW


def _launchArgvDialog(context):
    if globs.executor is None:
        return
    d = GetArgvDialog(globs.executor.state)
    d.exec_()
    ui_sync_view(globs.executor.state, True)


def _registerDynamicWidgets():
    dock_handler = DockHandler.getActiveDockHandler()
    dock_handler.addDockWidget(
        "SENinja Registers",
        _get_registerview_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )
    dock_handler.addDockWidget(
        "SENinja Memory",
        _get_memoryview_widget,
        Qt.BottomDockWidgetArea,
        Qt.Horizontal,
        False
    )
    dock_handler.addDockWidget(
        "SENinja Buffers",
        _get_buffer_view_widget,
        Qt.RightDockWidgetArea,
        Qt.Vertical,
        False
    )


def _registerUIActions():
    UIAction.registerAction("SENinja\\Setup argv...")
    UIActionHandler.globalActions().bindAction(
        "SENinja\\Setup argv...", UIAction(_launchArgvDialog))
    Menu.mainMenu("Tools").addAction("SENinja\\Setup argv...", "Setup argv...")


def enable_widgets():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None

    BNWidgets.RW.setEnabled(True)
    BNWidgets.MW.setEnabled(True)
    BNWidgets.BW.setEnabled(True)


def disable_widgets():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None

    BNWidgets.RW.setEnabled(False)
    BNWidgets.MW.setEnabled(False)
    BNWidgets.BW.setEnabled(False)


def ui_set_arch(arch, state):
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None

    BNWidgets.RW.init(arch, state)
    BNWidgets.MW.init(arch, state)
    BNWidgets.BW.init(state)


def ui_sync_view(state, delta=True):
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None

    if BNWidgets.RW.isVisible():
        BNWidgets.RW.set_reg_values(state)
    if BNWidgets.MW.isVisible():
        if delta:
            BNWidgets.MW.update_mem_delta(state)
        else:
            BNWidgets.MW.update_mem(state)
    if BNWidgets.BW.isVisible():
        BNWidgets.BW.update_state(state)


def ui_reset_view():
    assert BNWidgets.RW is not None
    assert BNWidgets.MW is not None
    assert BNWidgets.BW is not None

    BNWidgets.RW.reset()
    BNWidgets.MW.reset()
    BNWidgets.BW.reset()


_registerDynamicWidgets()
_registerUIActions()
