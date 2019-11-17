from memory.memory_abstract import MemoryAbstract
from utility.z3_wrap_util import symbolic, split_bv
from copy import deepcopy
import math
import z3

class Page(object):
    def __init__(self, addr, size, index_bits):
        self.addr = addr
        self.size = size
        self.index_bits = index_bits
        self.max_index = 2**index_bits - 1
        self._data = {}
        self._lazycopy = False
    
    def read(self, index: int):
        assert 0 <= index <= self.max_index
        if index not in self._data:
            self._data[index] = z3.BitVec('page_%x_i%d' % (self.addr, index), 8)
        return z3.simplify(self._data[index])
    
    def write(self, index: int, data: z3.BitVecRef):
        assert 0 <= index <= self.max_index
        assert data.size() == 8
        if self._lazycopy:
            self._lazycopy = False
            new_page = Page(self.addr, self.size, self.index_bits)
            new_page._data = deepcopy(self._data)
            return new_page.write(index, data)
        
        self._data[index] = data
        return self
    
    def copy(self):
        self._lazycopy = True
        return self

class MemoryConcreteFlat(MemoryAbstract):
    def __init__(self, state, page_size=0x100, bits=64):
        assert (page_size & (page_size - 1)) == 0  # page_size must be a power of 2
        self.bits       = bits
        self.state      = state
        self.pages      = dict()
        self.page_size  = page_size
        self.index_bits = math.ceil(math.log(page_size, 2))
    
    def mmap(self, address: int, size: int, init=None):
        assert address % self.page_size == 0
        assert size % self.page_size == 0
        for a in range(address // self.page_size, address // self.page_size + size // self.page_size, 1):
            self.pages[a] = Page(a * self.page_size, self.page_size, self.index_bits)

    def _store(self, page_address:int, page_index:int, value:z3.BitVecRef):
        assert value.size() == 8
        assert page_address in self.pages
        self.pages[page_address] = self.pages[page_address].write(page_index, value)

    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness='big'):
        assert not symbolic(address)

        address = address.as_long()
        size    = value.size()

        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                addr = address + i
            else:
                addr = address + size // 8 - i - 1

            page_address  = addr >> self.index_bits
            page_index    = addr - (page_address << self.index_bits)

            self._store(page_address, page_index, z3.simplify(z3.Extract(8*(i+1)-1, 8*i, value)))
    
    def _load(self, page_address:int, page_index:int):
        assert page_address in self.pages
        return self.pages[page_address].read(page_index)

    def load(self, address: z3.BitVecRef, size: int, endness='big'):
        assert not symbolic(address)

        address = address.as_long()

        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        res = None
        for i in ran:
            addr = address + i
            page_address  = addr >> self.index_bits
            page_index    = addr - (page_address << self.index_bits)

            tmp = self._load(page_address, page_index)
            res = tmp if res is None else z3.Concat(res, tmp)
        
        return z3.simplify(res)

    def get_unmapped(self, size, start_from, from_end):
        raise NotImplementedError
    
    def allocate(self, size):
        raise NotImplementedError

    def copy(self, state):
        new_memory = MemoryConcreteFlat(state, self.page_size, self.bits)
        new_pages  = dict()
        for page_addr in self.pages:
            new_pages[page_addr] = self.pages[page_addr].copy()
        new_memory.pages = new_pages
        return new_memory
