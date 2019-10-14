from utility.z3_wrap_util import bvv, bvs
from memory.sym_flat_memory import MemoryConcreteFlat
from IPython import embed
import math

class Regs(object):

    attr = {'state', 'bits', '_mem', '_regs', '_tmp_regs', 'flags'}

    def __init__(self, state):
        self.state     = state
        self.bits      = state.arch.bits()
        self._mem      = MemoryConcreteFlat(state, self.bits // 8, self.bits)
        self._regs     = dict()
        self._tmp_regs = dict()
        self.flags     = dict()

        regs_data = state.arch.regs_data()
        for reg_name in regs_data:
            reg_info = regs_data[reg_name]
            self._mem.mmap(reg_info["addr"], reg_info["size"])

            self._regs[reg_name] = reg_info["addr"], reg_info["size"]
            for subreg_name in reg_info["sub"]:
                subreg_info = reg_info["sub"][subreg_name]
                self._regs[subreg_name] = reg_info["addr"] + subreg_info["offset"], subreg_info["size"]
        
        for flag_name in state.arch.flags_data():
            self.flags[flag_name] = bvs(flag_name, 1)
    
    def has_reg(self, reg_name: str):
        return reg_name in self._regs

    def __getattribute__(self, k):
        if k in dir(Regs) or k in Regs.attr:
            return super().__getattribute__(k)
        if k not in self._regs and k not in self._tmp_regs:
            raise AttributeError("'%s' object has not attribute '%s'" % (self.__class__.__name__, k))
        if k in self._regs:
            reg_addr, reg_size = self._regs[k]
            return self._mem.load(bvv(reg_addr, self.bits), reg_size, endness='big')
        return self._tmp_regs[k]
    
    def __setattr__(self, k, val):
        if k in dir(Regs) or k in Regs.attr:
            return super().__setattr__(k, val)
        if k not in self._regs and "temp" not in k:
            raise AttributeError("'%s' object has not attribute '%s'" % (self.__class__.__name__, k))
        if k in self._regs:
            reg_addr, reg_size = self._regs[k]
            assert reg_size * 8 == val.size()
            self._mem.store(bvv(reg_addr, self.bits), val, endness='big')
        self._tmp_regs[k] = val

    def copy(self, state):
        new_regs = Regs(state)
        new_regs._mem = self._mem.copy(state)
        return new_regs
