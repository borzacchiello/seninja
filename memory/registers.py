from utility.z3_wrap_util import bvv
from memory.sym_memory import Memory
from IPython import embed
import math

class Regs(object):

    attr = {'state', 'bits', '_mem', '_regs'}

    def __init__(self, state):
        self.state = state
        self.bits  = state.arch.bits()
        self._mem  = Memory(state, self.bits // 8, self.bits)
        self._regs = dict()

        regs_data = state.arch.regs_data()
        for reg_name in regs_data:
            reg_info = regs_data[reg_name]
            self._mem.mmap(reg_info["addr"], reg_info["size"])

            self._regs[reg_name] = reg_info["addr"], reg_info["size"]
            for subreg_name in reg_info["sub"]:
                subreg_info = reg_info["sub"][subreg_name]
                self._regs[subreg_name] = reg_info["addr"] + subreg_info["offset"], subreg_info["size"]
    
    def __getattribute__(self, k):
        if k in dir(Regs) or k in Regs.attr:
            return super().__getattribute__(k)
        if k not in self._regs:
            raise AttributeError("'%s' object has not attribute '%s'" % (self.__class__.__name__, k))
        reg_addr, reg_size = self._regs[k]
        return self._mem.load(bvv(reg_addr, self.bits), reg_size, endness='big')
    
    def __setattr__(self, k, val):
        if k in dir(Regs) or k in Regs.attr:
            return super().__setattr__(k, val)
        if k not in self._regs:
            raise AttributeError("'%s' object has not attribute '%s'" % (self.__class__.__name__, k))
        reg_addr, reg_size = self._regs[k]
        assert reg_size * 8 == val.size()
        self._mem.store(bvv(reg_addr, self.bits), val, endness='big')

    def copy(self, state):
        new_regs = Regs(state)
        new_regs._mem = self._mem.copy(state)
        return new_regs
