from arch.arch_x86 import x86Arch
from utility.z3_wrap_util import symbolic
import z3

def get_arg_k(state, k):
    assert isinstance(state.arch, x86Arch)  # TODO implement various callng conventions

    stack_pointer = getattr(state.regs, state.arch.get_stack_pointer_reg())
    assert not symbolic(stack_pointer)

    return state.mem.load(stack_pointer + (state.arch.bits() // 8)*k, state.arch.bits() // 8, state.arch.endness())
