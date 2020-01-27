from ..utility.expr_wrap_util import symbolic
from ..expr import BV, BVS
from .memory_abstract import MemoryAbstract

class MemoryConcreteFlatNotPaged(MemoryAbstract):
    def __init__(self, name, bits=64):
        self.name   = name
        self.bits   = bits
        self.values = {}
        self._lazycopy = False
    
    def _handle_lazycopy(self):
        if self._lazycopy:
            self._lazycopy = False
            old_dict = self.values
            self.values = {}
            for addr in old_dict:
                self.values[addr] = old_dict[addr]

    def mmap(self, address: int, size: int, init=None):
        pass  # do nothing

    def store(self, address: BV, value: BV, endness='big'):
        assert not symbolic(address)
        self._handle_lazycopy()

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
                self.values[address+i] = BVS('unconstrained_{name}_{address}'.format(
                    name = self.name,
                    address = address + i,
                ), 8)

            tmp = self.values[address+i]
            res = tmp if res is None else res.Concat(tmp)

        return res

    def get_unmapped(self, size, start_from, from_end):
        raise NotImplementedError

    def allocate(self, size):
        raise NotImplementedError

    def copy(self, state=None):
        self._lazycopy = True
        res = MemoryConcreteFlatNotPaged(self.name, self.bits)
        res.values = self.values
        res._lazycopy = True
        return res
