from ..arch.arch_x86 import x86Arch
from .expr_wrap_util import symbolic
from .bninja_util import get_function


def get_arg_k(state, k, size, view):

    ip = state.get_ip()
    func = get_function(view, ip)
    calling_convention = func.calling_convention.name

    args = state.arch.get_argument_regs(calling_convention)
    if k-1 < len(args):
        res = getattr(state.regs, args[k-1])
        return res.Extract(8*size-1, 0)
    else:
        stack_pointer = getattr(state.regs, state.arch.get_stack_pointer_reg())
        assert not symbolic(stack_pointer)

        return state.mem.load(stack_pointer + (state.arch.bits() // 8)*(k - len(args)), size, state.arch.endness())
