import traceback
import os

from binaryninjaui import Sidebar
from binaryninja import PluginCommand
from .utility.expr_wrap_util import split_bv_in_list
from .utility.bninja_util import get_address_after_merge
from .utility.string_util import (
    int_to_str,
    str_to_int,
    as_bytes,
    get_byte,
    str_to_bv_list,
    str_to_bv,
    constraint_alphanumeric_string,
    constraint_ascii_string
)
from .models import function_models as seninja_models
from .expr import BVV, BVS, BV, And, Or, ITE
from . import settings
from .apis import (
    get_current_state,
    register_hook,
    register_logger,
    get_stdin_bv,
    get_stdout_bv,
    reload_settings
)

from .globals import Globals
from .ui.ui_manager import UIManager
from .ui.seninja_widget import SENinjaWidgetType

Globals.uimanager = UIManager()

Sidebar.addSidebarWidgetType(SENinjaWidgetType())

PluginCommand.register(
    "SENinja\\Setup argv...",
    "Setup argv for the current function",
    lambda bv: Globals.uimanager.launch_argv_dialog()
)
PluginCommand.register_for_address(
    "SENinja\\Select state",
    "Select the state at the current address",
    lambda bv, addr: Globals.uimanager.async_change_current_state(addr)
)
PluginCommand.register_for_address(
    "SENinja\\Merge states",
    "Merge all the states at the current address",
    lambda bv, addr: Globals.uimanager.async_merge_states(addr)
)
PluginCommand.register_for_address(
    "SENinja\\Mark as address to reach",
    "Set the destination address",
    lambda bv, addr: Globals.uimanager.set_run_target(addr)
)
PluginCommand.register_for_address(
    "SENinja\\Mark as address to avoid",
    "Set the avoid address",
    lambda bv, addr: Globals.uimanager.set_run_avoid(addr)
)
