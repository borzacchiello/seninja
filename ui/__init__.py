import seninja.seninja_globals as globs
from PySide2.QtWidgets import QApplication
from binaryninjaui import DockHandler, UIAction, UIActionHandler, Menu
from PySide2.QtCore import Qt
from .registers_view import RegisterView
from .memory_view import MemoryView
from .buffer_view import BufferView
from .argv_form import GetArgvDialog

RW = None
MW = None
BW = None


def _get_registerview_widget(name, parent, data):
    global RW
    RW = RegisterView(parent, name, data)
    RW.setEnabled(False)
    return RW


def _get_memoryview_widget(name, parent, data):
    global MW
    MW = MemoryView(parent, name, data)
    MW.setEnabled(False)
    return MW


def _get_buffer_view_widget(name, parent, data):
    global BW
    BW = BufferView(parent, name, data)
    BW.setEnabled(False)
    return BW


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
    assert RW is not None
    assert MW is not None
    assert BW is not None

    RW.setEnabled(True)
    MW.setEnabled(True)
    BW.setEnabled(True)


def disable_widgets():
    assert RW is not None
    assert MW is not None
    assert BW is not None

    RW.setEnabled(False)
    MW.setEnabled(False)
    BW.setEnabled(False)


def ui_set_arch(arch, state):
    assert RW is not None
    assert MW is not None
    assert BW is not None

    RW.init(arch, state)
    MW.init(arch, state)
    BW.init(state)


def ui_sync_view(state, delta=True):
    assert RW is not None
    assert MW is not None
    assert BW is not None

    if RW.isVisible():
        RW.set_reg_values(state)
    if MW.isVisible():
        if delta:
            MW.update_mem_delta(state)
        else:
            MW.update_mem(state)
    if BW.isVisible():
        BW.update_state(state)


def ui_reset_view():
    assert RW is not None
    assert MW is not None
    assert BW is not None

    RW.reset()
    MW.reset()
    BW.reset()


_registerDynamicWidgets()
_registerUIActions()
