from ..seninja_globals import globs
from PySide6.QtWidgets import QApplication
from binaryninjaui import UIContext, UIAction, UIActionHandler, Menu, Sidebar
from PySide6.QtCore import Qt
from .seninja_widget import SENinjaWidgetType
from .state_view import StateView
from .control_view import ControlView
from .memory_view import MemoryView
from .buffer_view import BufferView
from .argv_form import GetArgvDialog

def get_widget(name):
    ctx = UIContext.activeContext()
    if ctx is None:
        return None
    view_frame = ctx.getCurrentViewFrame()
    if view_frame is None:
        return None
    sidebar = view_frame.getSidebar()
    if sidebar is None:
        return None
    return sidebar.widget(name)

def _launchArgvDialog(context):
    if globs.executor is None:
        return
    d = GetArgvDialog(globs.executor.state)
    d.exec_()
    ui_sync_view(globs.executor.state, True)

def _registerDynamicWidgets():
    Sidebar.addSidebarWidgetType(SENinjaWidgetType())

def _registerUIActions():
    UIAction.registerAction("SENinja\\Setup argv...")
    UIActionHandler.globalActions().bindAction(
        "SENinja\\Setup argv...", UIAction(_launchArgvDialog))
    Menu.mainMenu("Tools").addAction("SENinja\\Setup argv...", "Setup argv...")

def ui_set_arch(arch, state):
    widget = get_widget(SENinjaWidgetType.name)
    if widget is None:
        return
    widget.initSignal.emit(arch, state)

def ui_sync_view(state, delta=True):
    widget = get_widget(SENinjaWidgetType.name)
    if widget is None:
        return
    widget.updateStateSignal.emit(state)

def ui_reset_view():
    widget = get_widget(SENinjaWidgetType.name)
    if widget is None:
        return
    widget.resetSignal.emit()

def enable_widgets():
    pass

def disable_widgets():
    pass

_registerDynamicWidgets()
_registerUIActions()
