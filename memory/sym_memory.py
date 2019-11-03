from utility.z3_wrap_util import symbolic, split_bv, bvv_to_long, bvv, heuristic_find_base
from memory.memory_object import MemoryObj
from memory.memory_abstract import MemoryAbstract
from collections import namedtuple
from options import (
    HEURISTIC_UNCONSTRAINED_MEM_ACCESS,
    CHECK_IF_MEM_ACCESS_IS_TOO_LARGE
)
from utility.error_codes import ErrorInstruction
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

        self.mo.store(index, value, condition)
        return self
    
    def load(self, index: z3.BitVecRef):
        self.lazy_init()
        return self.mo.load(index)

    def copy(self):
        self._lazycopy = True
        return self

class Memory(MemoryAbstract):
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
            data_index_i = 0
            data_index_f = self.page_size - init_index

        i = 0
        for a in range(address // self.page_size, address // self.page_size + size // self.page_size, 1):
            if a not in self.pages:
                init_data = None
                if init_index is not None:
                    init_data = InitData(
                        init_val[data_index_i : data_index_f],
                        init_index)
                    init_index = 0  # only the first page has a starting index
                    data_index_i = data_index_f
                    data_index_f = data_index_i + self.page_size
                self.pages[a] = Page(a, self.page_size, self.index_bits, init_data)
            else:
                print("remapping the same page '%s'" % hex(a))
            i+=1
    
    def _handle_symbolic_address(self, address: z3.BitVecRef, size: int, op_type: str):
        max_addr = self.state.solver.max(address)
        min_addr = self.state.solver.min(address)
        if (
            HEURISTIC_UNCONSTRAINED_MEM_ACCESS and
            symbolic(address) and
            max_addr - min_addr == 2**self.state.arch.bits() - 1 and
            heuristic_find_base(address) == -1
        ):
            address_conc = self.get_unmapped(size // self.page_size + 1, False) * self.page_size
            self.mmap(address_conc, (size // self.page_size + 1) * self.page_size)
            self.state.solver.add_constraints(address == address_conc)
            print("WARNING: %s, concretizing mem access (heuristic unconstrained)" % op_type)
            address = bvv(address_conc, address.size())

        if (
            CHECK_IF_MEM_ACCESS_IS_TOO_LARGE and
            symbolic(address)
        ):
            if max_addr - min_addr > 3 * self.page_size:
                print("WARNING: %s, limiting mem access (too broad)" % op_type)

                if min_addr == 0 and max_addr == 2 ** self.bits - 1:
                    # unconstrained case
                    address_conc = self.get_unmapped(size // self.page_size + 1, False) * self.page_size
                    self.mmap(address_conc, (size // self.page_size + 1) * self.page_size)
                    self.state.solver.add_constraints(address == address_conc)
                    print("\tconcretizing mem access to a new page (unconstrained)")
                    address = bvv(address_conc, address.size())
                
                else:
                    # limit page near a pivot
                    page_address, _ = split_bv(address, self.index_bits)
                    pivot = (min_addr + self.page_size) >> self.index_bits
                    base = heuristic_find_base(address)
                    if base != -1 and min_addr <= base <= max_addr:
                        print("\theurstic base: %s" % hex(base))
                        pivot = base >> self.index_bits
                    
                    # for i in range(pivot-1, pivot+2):
                    #     if i not in self.pages:
                    #         print("\tmapping page %s" % hex(i))
                    #         self.mmap(i*self.page_size, self.page_size)
                    self.state.solver.add_constraints(page_address >= pivot - 1, page_address <= pivot + 1)
        return address
    
    def _store(self, page_address: int, page_index: z3.BitVecRef, value: z3.BitVecRef, condition: z3.BoolRef=None):
        assert page_address in self.pages
        assert value.size() == 8
        
        self.pages[page_address] = self.pages[page_address].store(page_index, value, condition)
    
    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness='big'):
        assert address.size() == self.bits

        address = self._handle_symbolic_address(address, value.size(), "store")

        page_addresses = set()
        conditions     = list()
        size           = value.size()
        assert size % 8 == 0
        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                page_address, page_index = split_bv(address + i, self.index_bits)
            else:
                page_address, page_index = split_bv(address + size // 8 - i - 1, self.index_bits)

            if not symbolic(page_address):  # only syntactic check.
                page_address = bvv_to_long(page_address)
                page_addresses.add(page_address)
                self._store(page_address, page_index, z3.Extract(8*(i+1)-1, 8*i, value))
            elif not self.state.solver.symbolic(page_address): # check with path constraint
                page_address = self.state.solver.evaluate_long(page_address)
                page_addresses.add(page_address)
                self._store(page_address, page_index, z3.Extract(8*(i+1)-1, 8*i, value))
            else: # symbolic access
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
                if not self.state.solver.satisfiable(extra_constraints=[
                    z3.simplify(z3.Or(*conditions))
                ]):
                    self.state.executor.fringe.errored.append(
                        (self.state, "write unmapped")
                    )
                    self.state.executor.state = None
                    return ErrorInstruction.UNMAPPED_WRITE

                errored_state = self.state.copy()
                errored_state.solver.add_constraints(z3.simplify(z3.Not(z3.Or(*conditions))))
                self.state.executor.fringe.errored.append(
                    (errored_state, "write unmapped")
                )
                self.state.solver.add_constraints(z3.simplify(z3.Or(*conditions)))
        
        # simplify accessed pages
        for p in page_addresses:
            self.pages[p].mo.simplify()

    def _load(self, page_address: int, page_index: z3.BitVecRef):
        assert page_address in self.pages
        return self.pages[page_address].load(page_index)
    
    def load(self, address: z3.BitVecRef, size: int, endness='big'):
        assert address.size() == self.bits

        address = self._handle_symbolic_address(address, size, "load")

        res = None
        conditions = list()
        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        for i in ran:
            page_address, page_index = split_bv(address + i, self.index_bits)
            if not symbolic(page_address): # syntactic check
                page_address = bvv_to_long(page_address)
                tmp = z3.simplify(self._load(page_address, page_index))
            elif not self.state.solver.symbolic(page_address): # check with path constraint
                page_address = self.state.solver.evaluate_long(page_address)
                tmp = z3.simplify(self._load(page_address, page_index))
            else: # symbolic access
                conditions = list()
                tmp = None
                for p in self.pages:  # can be improved?
                    if self.state.solver.satisfiable(extra_constraints=[
                        page_address == p
                    ]):
                        condition = z3.simplify(p == page_address)
                        conditions.append(condition)
                        tmp = z3.If(condition,
                                self._load(p, page_index),
                                tmp
                        ) if tmp is not None else self._load(p, page_index)
            res = tmp if res is None else z3.Concat(res, tmp)

        if conditions:
            if not self.state.solver.satisfiable(extra_constraints=[
                z3.simplify(z3.Or(*conditions))
            ]):
                self.state.executor.fringe.errored.append(
                    (self.state, "read unmapped")
                )
                self.state.executor.state = None
                return ErrorInstruction.UNMAPPED_READ

            errored_state = self.state.copy()
            errored_state.solver.add_constraints(z3.simplify(z3.Not(z3.Or(*conditions))))
            self.state.executor.fringe.errored.append(
                (errored_state, "read unmapped")
            )
            self.state.solver.add_constraints(z3.simplify(z3.Or(*conditions)))

        assert res is not None
        assert res.size() // 8 == size
        return z3.simplify(res)

    def get_unmapped(self, size, from_end=True):
        last_page = 2**(self.bits - self.index_bits) - 4
        i     = last_page if from_end else 2
        j     = 2
        count = 0

        while j <= last_page and count != size:
            if i not in self.pages:
                count += 1
            else:
                count  = 0
                if not from_end:
                    i = j+1
            j += 1
            if from_end:
                i -= 1
        return i
    
    def copy(self, state):
        new_memory = Memory(state, self.page_size, self.bits)
        new_pages  = dict()
        for page_addr in self.pages:
            new_pages[page_addr] = self.pages[page_addr].copy()
        new_memory.pages = new_pages
        return new_memory
    
    def merge(self, other, merge_condition: z3.BoolRef):
        assert isinstance(other, Memory)
        for page_addr in other.pages:
            other_page = other.pages[page_addr]

            if page_addr in self.pages and self.pages[page_addr].mo._z3obj.eq(other_page.mo._z3obj):
                continue  # very same page. No need to update
            
            if page_addr not in self.pages:
                self.mmap(page_addr, self.page_size)

            self.pages[page_addr].mo._z3obj = z3.simplify(
                z3.If(
                    merge_condition, 
                    other_page.mo._z3obj, 
                    self.pages[page_addr].mo._z3obj
                )
            )
