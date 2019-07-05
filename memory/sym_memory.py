from utility.z3_wrap_util import symbolic, split_bv, bvv_to_long, bvv
from memory.memory_object import MemoryObj
from collections import namedtuple
import math
import z3
from IPython import embed

InitData = namedtuple('InitData', ['bytes', 'index'])  # bytes: byte array; index: int

class Page(object):
    def __init__(self, addr: int, size: int=0x1000, bits: int=12, init: InitData=None):
        self.addr = addr
        self.size = size
        self.bits = bits
        self.mo   = MemoryObj(str(addr), bits)
        self._init     = init
        self._lazycopy = False
    
    def lazy_init(self):
        if self._init is not None:
            start = bvv(self._init.index, self.bits)
            val   = self._init.bytes
            assert len(val) + self._init.index <= self.size
            for i in range(len(val)):
                subval = val[i]
                self.mo.store(start + i, bvv(subval, 8))
            self._init = None
    
    def store(self, index: z3.BitVecRef, value: z3.BitVecRef, condition: z3.BoolRef=None):
        self.lazy_init()
        if self._lazycopy:
            self._lazycopy = False
            new_page = Page(self.addr, self.size, self.bits)
            new_page.mo = self.mo.copy()
            return new_page.store(index, value)

        self.mo.store(index, value)
        return self
    
    def load(self, index: z3.BitVecRef):
        self.lazy_init()
        return self.mo.load(index)

    def copy(self):
        self._lazycopy = True
        return self

class Memory(object):
    def __init__(self, state, page_size=0x1000, bits=64):
        assert (page_size & (page_size - 1)) == 0  # page_size must be a power of 2
        self.bits       = bits
        self.state      = state
        self.pages      = dict()
        self.page_size  = page_size
        self.index_bits = math.ceil(math.log(page_size, 2))
    
    def mmap(self, address: int, size: int, init: InitData=None):
        assert address % self.page_size == 0
        assert size % self.page_size == 0

        init_val   = None
        init_index = None
        if init is not None:
            init_val   = init.bytes
            init_index = init.index

        i = 0
        for a in range(address // self.page_size, address // self.page_size + size // self.page_size, 1):
            if a not in self.pages:
                init_data = None
                if init_index is not None:
                    init_data = InitData(
                        init_val[i*self.page_size : (i+1)*self.page_size - init_index],
                        init_index)
                    init_index = 0  # only the first page has a starting index
                self.pages[a] = Page(a, self.page_size, self.index_bits, init_data)
            else:
                print("remapping the same page '%s'" % hex(a))
            i+=1
    
    def _store(self, page_address: int, page_index: z3.BitVecRef, value: z3.BitVecRef, condition: z3.BoolRef=None):
        assert page_address in self.pages
        assert value.size() == 8
        
        self.pages[page_address] = self.pages[page_address].store(page_index, value, condition)
    
    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness='big'):
        assert address.size() == self.bits

        page_addresses = set()
        conditions     = list()
        size           = value.size()
        assert size % 8 == 0
        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                page_address, page_index = split_bv(address + i, self.index_bits)
            else:
                page_address, page_index = split_bv(address + size // 8 - i - 1, self.index_bits)

            if not symbolic(page_address):
                page_address = bvv_to_long(page_address)
                page_addresses.add(page_address)
                self._store(page_address, page_index, z3.Extract(8*(i+1)-1, 8*i, value))
            else:
                page_address = z3.simplify(page_address)
                page_index   = z3.simplify(page_index)
                conditions   = list()
                for p in self.pages:  # can be improved?
                    if self.state.solver.satisfiable(extra_constraints=[
                        page_address == p
                    ]):
                        page_addresses.add(p)
                        condition = z3.simplify(p == page_address)
                        conditions.append(condition)
                        self._store(p, page_index, z3.Extract(8*(i+1)-1, 8*i, value), condition)
            if conditions:
                self.state.solver.add_constraints(z3.simplify(z3.Or(*conditions)))
        
        # simplify accessed pages
        for p in page_addresses:
            self.pages[p].mo.simplify()

    def _load(self, page_address: int, page_index: z3.BitVecRef):
        assert page_address in self.pages
        return self.pages[page_address].load(page_index)
    
    def load(self, address: z3.BitVecRef, size: int, endness='big'):
        assert address.size() == self.bits

        res = None
        conditions = list()
        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        for i in ran:
            page_address, page_index = split_bv(address + i, self.index_bits)
            if not symbolic(page_address):
                page_address = bvv_to_long(page_address)
                tmp = z3.simplify(self._load(page_address, page_index))
                res = tmp if res is None else z3.Concat(res, tmp)
            else:
                conditions = list()
                for p in self.pages:  # can be improved?
                    if self.state.solver.satisfiable(extra_constraints=[
                        page_address == p
                    ]):
                        condition = z3.simplify(p == page_address)
                        conditions.append(condition)
                        res = z3.If(condition,
                                self._load(p, page_index),
                                res
                        ) if res is not None else self._load(p, page_index)
        if conditions:
            errored_state = self.state.copy()
            errored_state.solver.add_constraints(z3.simplify(z3.Not(z3.Or(*conditions))))
            self.state.executor.fringe.errored.append(
                (errored_state, "read unmapped")
            )
            self.state.solver.add_constraints(z3.simplify(z3.Or(*conditions)))

        return z3.simplify(res)
    
    def copy(self):
        new_memory = Memory(self.state, self.page_size, self.bits)
        new_pages  = dict()
        for page_addr in self.pages:
            new_pages[page_addr] = self.pages[page_addr].copy()
        new_memory.pages = new_pages
        return new_memory
