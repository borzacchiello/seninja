from ..utility.expr_wrap_util import symbolic
from ..expr import BV, BVS
from .memory_abstract import MemoryAbstract

class MemoryConcreteFlatNotPaged(MemoryAbstract):
    def __init__(self, state, bits=64):
        self.bits   = bits
        self.state  = state
        self.values = {}
    
    def mmap(self, address: int, size: int, init=None):
        pass  # do nothing

    def store(self, address: BV, value: BV, endness='big'):
        assert not symbolic(address)

        address = address.value
        size    = value.size

        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                addr = address + i
            else:
                addr = address + size // 8 - i - 1
            self.values[addr] = value.Extract(8*(i+1)-1, 8*i)

    def load(self, address: BV, size: int, endness='big'):
        assert not symbolic(address)

        address = address.value

        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        res = None
        for i in ran:
            if (address+i) not in self.values:
                self.values[address+i] = BVS('FlatMemUnconstrained_%x' % (address+i), 8)

            tmp = self.values[address+i]
            res = tmp if res is None else res.Concat(tmp)

        return res

    def get_unmapped(self, size, start_from, from_end):
        raise NotImplementedError

    def allocate(self, size):
        raise NotImplementedError

    def copy(self, state):
        new_memory = MemoryConcreteFlatNotPaged(state, self.bits)
        for addr in self.values:
            new_memory.values[addr] = self.values[addr]
        return new_memory
