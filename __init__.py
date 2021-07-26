import traceback
import os
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
from .apis_ui import (
    _async_start_se,
    _async_change_current_state,
    _async_step,
    _async_continue_until_branch,
    _async_continue_until_address,
    _async_merge_states,
    _async_save_active_state,
    _async_change_active_state_ip,
    _set_run_target,
    _set_run_avoid,
    _async_run_dfs_searcher,
    _async_run_dfs_searcher_findall,
    _async_run_bfs_searcher,
    _async_reset_se,
    _async_toggle_state_history,
    sync_ui
)
from .apis import (
    start_se,
    reset_se,
    continue_until_branch,
    setup_argv,
    execute_one_instruction,
    stop,
    get_current_state,
    get_executor,
    register_hook,
    register_logger,
    get_stdin_bv,
    reload_settings
)

PluginCommand.register_for_address(
    "SENinja\\0   Start symbolic execution",
    "create the first state for symbolic execution at current address",
    _async_start_se
)
PluginCommand.register_for_address(
    "SENinja\\1   Change current state",
    "change current state with the deferred one at current address (if any)",
    _async_change_current_state
)
PluginCommand.register(
    "SENinja\\2   Step",
    "execute one instruction with the current state",
    _async_step
)
PluginCommand.register_for_address(
    "SENinja\\3   Merge states",
    "merge all states at current address in one state",
    _async_merge_states
)
PluginCommand.register(
    "SENinja\\4   Save active state",
    "save active state in deferred queue",
    _async_save_active_state
)
PluginCommand.register_for_address(
    "SENinja\\5   Set IP to address",
    "set ip of active state to current address",
    _async_change_active_state_ip
)
PluginCommand.register(
    "SENinja\\6   Toggle state history",
    "highlight instructions executed by the current syaye",
    _async_toggle_state_history
)
PluginCommand.register(
    "SENinja\\7   Run\\1   Continue until branch",
    "execute instructions in the current state until a fork occurs",
    _async_continue_until_branch
)
PluginCommand.register_for_address(
    "SENinja\\7   Run\\2   Continue until address",
    "execute instructions in the current state until the currently selected address is reached",
    _async_continue_until_address
)
PluginCommand.register_for_address(
    "SENinja\\7   Run\\3   Set searcher target",
    "set run target",
    _set_run_target
)
PluginCommand.register_for_address(
    "SENinja\\7   Run\\4   Set searcher avoid",
    "set run avoid",
    _set_run_avoid
)
PluginCommand.register(
    "SENinja\\7   Run\\5   Run (DFS)",
    "run (target must be set)",
    _async_run_dfs_searcher
)
PluginCommand.register(
    "SENinja\\7   Run\\6   Run (DFS) findall",
    "run (target must be set)",
    _async_run_dfs_searcher_findall
)
PluginCommand.register(
    "SENinja\\7   Run\\7   Run (BFS)",
    "run (target must be set)",
    _async_run_bfs_searcher
)
PluginCommand.register_for_address(
    "SENinja\\8   Reset",
    "delete all states",
    _async_reset_se
)
