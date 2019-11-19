from arch.arch_abstract import Arch
from arch.arch_x86_64 import x8664Arch
from os_models.os_abstract import Os
from os_models.linux import Linuxia64
from memory.registers import Regs
from memory.sym_memory import Memory
from sym_solver import Solver
from utility.expr_wrap_util import symbolic
from expr import BV, BVV

class State(object):
    def __init__(self, executor, os: Os, arch: Arch=x8664Arch(), page_size: int=0x1000):
        self.page_size      = page_size
        self.arch           = arch
        self.mem            = Memory(self, page_size, arch.bits())
        self.regs           = Regs(self)
        self.solver         = Solver(self)
        self.os             = os
        self.events         = list()
        self.llil_ip        = None
        self.executor       = executor
    
    def get_ip(self):
        ip = getattr(self.regs, self.arch.getip_reg())
        assert not symbolic(ip)
        return ip.value
    
    def address_page_aligned(self, addr):
        return addr >> self.mem.index_bits << self.mem.index_bits

    def initialize_stack(self, stack_base):
        setattr(self.regs, self.arch.get_stack_pointer_reg(), BVV(stack_base, self.arch.bits()))
        setattr(self.regs, self.arch.get_base_pointer_reg(),  BVV(stack_base, self.arch.bits()))

    def stack_push(self, val: BV):
        stack_pointer     = getattr(self.regs, self.arch.get_stack_pointer_reg())
        new_stack_pointer = stack_pointer - self.arch.bits() // 8
        self.mem.store(new_stack_pointer, val, endness=self.arch.endness())
        setattr(self.regs, self.arch.get_stack_pointer_reg(), new_stack_pointer)
  
    def stack_pop(self):
        stack_pointer = getattr(self.regs, self.arch.get_stack_pointer_reg())
        res = self.mem.load(stack_pointer, self.arch.bits() // 8, endness=self.arch.endness())
        new_stack_pointer = stack_pointer + self.arch.bits() // 8
        setattr(self.regs, self.arch.get_stack_pointer_reg(), new_stack_pointer)
        return res
    
    def set_ip(self, new_ip):
        setattr(self.regs, self.arch.getip_reg(), BVV(new_ip, self.arch.bits()))

    def copy(self, solver_copy_fast=False):
        new_state = State(self.executor, self.os.copy(), self.arch, self.page_size)
        new_state.mem = self.mem.copy(new_state)
        new_state.regs = self.regs.copy(new_state)
        new_state.solver = self.solver.copy(new_state, solver_copy_fast)
        new_state.events = list(self.events)
        new_state.llil_ip = self.llil_ip

        return new_state

    def merge(self, other):
        assert isinstance(other, State)
        assert self.arch.__class__ == other.arch.__class__
        assert self.os.__class__ == other.os.__class__
        assert self.get_ip() == other.get_ip()
        assert self.llil_ip == other.llil_ip

        _, _, merge_condition = self.solver.compute_solvers_difference(other.solver)
        self.solver.merge(other.solver)
        self.mem.merge(other.mem, merge_condition)
        self.regs.merge(other.regs, merge_condition)
        self.os.merge(other.os, merge_condition)
        self.events.append(
            (
                "merged with %s" % str(other),
                other.events[:]  # TODO delete common events
            )
        )
