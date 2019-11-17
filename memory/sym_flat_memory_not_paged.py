from memory.memory_abstract import MemoryAbstract
from utility.z3_wrap_util import symbolic, split_bv
from copy import deepcopy
import math
import z3

class MemoryConcreteFlatNotPaged(MemoryAbstract):
    def __init__(self, state, bits=64):
        self.bits   = bits
        self.state  = state
        self.values = {}
    
    def mmap(self, address: int, size: int, init=None):
        pass  # do nothing

    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness='big'):
        assert not symbolic(address)

        address = address.as_long()
        size    = value.size()

        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                addr = address + i
            else:
                addr = address + size // 8 - i - 1
            self.values[addr] = z3.simplify(z3.Extract(8*(i+1)-1, 8*i, value))

    def load(self, address: z3.BitVecRef, size: int, endness='big'):
        assert not symbolic(address)
        
        address = address.as_long()

        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        res = None
        for i in ran:
            if (address+i) not in self.values:
                self.values[address+i] = z3.BitVec('FlatMemUnconstrained_%x' % (address+i), 8)

            tmp = self.values[address+i]
            res = tmp if res is None else z3.Concat(res, tmp)
        
        return z3.simplify(res)

    def get_unmapped(self, size, start_from, from_end):
        raise NotImplementedError
    
    def allocate(self, size):
        raise NotImplementedError

    def copy(self, state):
        new_memory = MemoryConcreteFlatNotPaged(state, self.bits)
        for addr in self.values:
            new_memory.values[addr] = self.values[addr]
        return new_memory

