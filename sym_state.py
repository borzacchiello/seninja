from arch.arch_abstract import Arch
from arch.arch_x86_64 import x8664Arch
from memory.registers import Regs
from memory.sym_memory import Memory
from sym_solver import Solver
from utility.z3_wrap_util import bvv, symbolic
from devices.device_manager import DeviceManager
import z3

class State(object):
    def __init__(self, executor, arch: Arch=x8664Arch(), page_size: int=0x1000):
        self.page_size      = page_size
        self.arch           = arch
        self.mem            = Memory(self, page_size, arch.bits())
        self.regs           = Regs(self)
        self.solver         = Solver(self)
        self.device_manager = DeviceManager(self)
        self.events         = list()
        self.executor       = executor
    
    def get_ip(self):
        ip = getattr(self.regs, self.arch.getip_reg())
        assert not symbolic(ip)
        return ip.as_long()
    
    def address_page_aligned(self, addr):
        return addr >> self.mem.index_bits << self.mem.index_bits

    def get_unmapped(self, size):
        return self.mem.get_unmapped(size)

    def initialize_stack(self, stack_base):
        setattr(self.regs, self.arch.get_stack_pointer_reg(), bvv(stack_base, self.arch.bits()))
        setattr(self.regs, self.arch.get_base_pointer_reg(),  bvv(stack_base, self.arch.bits()))

    def stack_push(self, val: z3.BitVecRef):
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
        setattr(self.regs, self.arch.getip_reg(), bvv(new_ip, self.arch.bits()))

    def copy(self):
        new_state = State(self.executor, self.arch, self.page_size)
        new_state.mem = self.mem.copy(new_state)
        new_state.regs = self.regs.copy(new_state)
        new_state.solver = self.solver.copy(new_state)
        new_state.device_manager = self.device_manager.copy(new_state)
        new_state.events = list(self.events)

        return new_state
