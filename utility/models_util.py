from arch.arch_x86 import x86Arch
from utility.z3_wrap_util import symbolic
from utility.bninja_util import get_function
import z3

def get_arg_k(state, k, view):
    
    ip = state.get_ip()
    func = get_function(view, ip)
    calling_convention = func.calling_convention.name

    if calling_convention == 'sysv':
        args = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
        if k-1 < len(args):
            return getattr(state.regs, args[k-1])
        else:
            stack_pointer = getattr(state.regs, state.arch.get_stack_pointer_reg())
            assert not symbolic(stack_pointer)

            return state.mem.load(stack_pointer + (state.arch.bits() // 8)*k, state.arch.bits() // 8, state.arch.endness())
    elif calling_convention == 'cdecl':
        stack_pointer = getattr(state.regs, state.arch.get_stack_pointer_reg())
        assert not symbolic(stack_pointer)

        return state.mem.load(stack_pointer + (state.arch.bits() // 8)*k, state.arch.bits() // 8, state.arch.endness())
    
    raise Exception("Unknown calling convention")

def get_result_reg(state, view, size):
    ip = state.get_ip()
    func = get_function(view, ip)
    calling_convention = func.calling_convention.name

    if calling_convention == 'cdecl':
        if size == 8:
            return 'al'
        elif size == 16:
            return 'ax'
        elif size == 32:
            return 'eax'
        else:
            raise Exception("invalid size") 
    elif calling_convention == 'sysv':
        if size == 8:
            return 'al'
        elif size == 16:
            return 'ax'
        elif size == 32:
            return 'eax'
        elif size == 64:
            return 'rax'
        else:
            raise Exception("invalid size")
    
    raise Exception("Unknown calling convention")
    
