import math

from collections import namedtuple
from ..utility.expr_wrap_util import symbolic, split_bv, heuristic_find_base 
from ..expr import BV, BVV, Bool, Or, ITE
from ..utility.error_codes import ErrorInstruction
from .memory_object import MemoryObj
from .memory_abstract import MemoryAbstract

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
            start = BVV(self._init.index, self.bits)
            val   = self._init.bytes
            assert len(val) + self._init.index <= self.size
            for i in range(len(val)):
                subval = val[i]
                self.mo.store(start + i, BVV(subval, 8))
            self._init = None
    
    def store(self, index: BV, value: BV, condition: Bool=None):
        self.lazy_init()
        if self._lazycopy:
            self._lazycopy = False
            new_page = Page(self.addr, self.size, self.bits)
            new_page.mo = self.mo.copy()
            return new_page.store(index, value)

        index = index.simplify()
        self.mo.store(index, value, condition)
        return self
    
    def load(self, index: BV):
        self.lazy_init()
        return self.mo.load(index)

    def copy(self):
        self._lazycopy = True
        return self

class Memory(MemoryAbstract):
    def __init__(self, state, page_size=0x1000, bits=64, symb_uninitialized=False):
        assert (page_size & (page_size - 1)) == 0  # page_size must be a power of 2
        self.bits        = bits
        self.state       = state
        self.pages       = dict()
        self.page_size   = page_size
        self.index_bits  = math.ceil(math.log(page_size, 2))
        self.symb_init   = symb_uninitialized
        self.load_hooks  = []
        self.store_hooks = []
    
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

        if not self.symb_init:
            # zero initialize
            if init_val is None:
                init_val   = b"\x00" * size
                init_index = 0
            init_val = b"\x00" * init_index + init_val                        # fill begin
            init_val = init_val + b"\x00" * (self.page_size % len(init_val))  # fill end
            init_index = 0
            data_index_i = 0
            data_index_f = self.page_size
        
        i = 0
        for a in range(
            address // self.page_size,
            address // self.page_size + size // self.page_size,
            1
        ):
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
    
    def is_mapped(self, address: int):
        return address >> self.index_bits in self.pages
    
    def _handle_symbolic_address(self, address: BV, size: int, op_type: str):

        if isinstance(address, BVV):
            return address, None, None
        if not self.state.solver.symbolic(address):  # check with solver
            return self.state.solver.evaluate(address), None, None
        
        print("WARNING: memory %s, symbolic memory access" % op_type)
        symb_access_mode            = self.state.executor.bncache.get_setting("memory.symb_address_mode")
        page_limit                  = int(self.state.executor.bncache.get_setting("memory.limit_pages_limit"))
        concretize_unconstrained    = self.state.executor.bncache.get_setting("memory.concretize_unconstrained") == 'true'
        use_heuristic_find_base     = self.state.executor.bncache.get_setting("memory.use_heuristic_find_base") == 'true'
        min_addr                    = None
        max_addr                    = None
        min_addr_approx             = address.interval.low
        max_addr_approx             = address.interval.high
        heuristic_base              = None

        if concretize_unconstrained:
            min_addr_approx = address.interval.low
            max_addr_approx = address.interval.high

            if max_addr_approx - min_addr_approx == 2**self.state.arch.bits() - 1:
                # slow path. let's use the solver to validate
                min_addr = self.state.solver.min(address)
                max_addr = self.state.solver.max(address)

                if max_addr - min_addr == 2**self.state.arch.bits() - 1:
                    # unconstrained case
                    print("WARNING: memory %s, concretizing mem access to a newly allocated address (\"concretize_unconstrained\" policy)" % op_type)
                    address_conc = self.get_unmapped(size // self.page_size + 1, from_end=False) * self.page_size
                    self.mmap(address_conc, (size // self.page_size + 1) * self.page_size)
                    self.state.solver.add_constraints(address == address_conc)
                    address = BVV(address_conc, address.size)
                    return address, min_addr, max_addr

        if symb_access_mode == "concretization":
            print("WARNING: memory %s, concretizing mem access (\"concretization\" policy)" % op_type)
            heuristic_base = heuristic_find_base(address) if heuristic_base is None else heuristic_base
            if use_heuristic_find_base and heuristic_base != -1 and self.state.solver.satisfiable([address == heuristic_base]):
                print("WARNING: memory %s, heuristic address 0x%x" % (op_type, heuristic_base))
                address_conc = BVV(heuristic_base, address.size)
            else:
                address_conc = self.state.solver.evaluate(address)
            self.state.solver.add_constraints(address == address_conc)
            return address_conc, None, None
      
        if symb_access_mode == "fully_symbolic":
            return (
                address_conc, 
                min_addr_approx if min_addr is None else min_addr,
                max_addr_approx if max_addr is None else max_addr
            )

        assert symb_access_mode == "limit_pages"
        assert page_limit > 0

        if max_addr_approx - min_addr_approx == 2**self.state.arch.bits() - 1:
            # slow path. let's use the solver to validate
            min_addr = self.state.solver.min(address) if min_addr is None else min_addr
            max_addr = self.state.solver.max(address) if max_addr is None else max_addr
            if max_addr - min_addr > page_limit * self.page_size:
                print("WARNING: memory %s, limiting memory access (\"limit_pages\" policy)" % op_type)

                min_addr_page = min_addr >> self.index_bits
                max_addr_page = max_addr >> self.index_bits
                page_address, _ = split_bv(address, self.index_bits)
                
                heuristic_base = heuristic_find_base(address) if heuristic_base is None else heuristic_base
                heuristic_base_page = heuristic_base >> self.index_bits

                if (
                    use_heuristic_find_base and 
                    heuristic_base != -1 and 
                    heuristic_base_page >= min_addr_page and
                    heuristic_base_page <= max_addr_page - page_limit and
                    self.state.solver.satisfiable([address == heuristic_base])
                ):
                    print("WARNING: memory %s, heuristic address 0x%x" % (op_type, heuristic_base))
                    pivot = heuristic_base_page
                else:
                    # make it more efficient! (interval tree?)
                    pages_in_range = [page for page in self.pages if (page >= min_addr_page and page <= max_addr_page)]

                    if pages_in_range:
                        pivot = min(pages_in_range)
                    else:
                        print("WARNING: memory %s, allocating pages (\"limit_pages\" policy)" % op_type)
                        pivot = self.get_unmapped(self.page_size * page_limit, from_end=False)
                        self.mmap(pivot << self.index_bits, page_limit * self.page_size)
                
                condition = None
                for i in range(page_limit):
                    condition = (page_address == pivot + i) if condition is None else (Or(condition, page_address == pivot + i))
                
                # I am not checking the satisfiability of every page, but at least the first one is satisfiable
                self.state.solver.add_constraints(condition)
                return address, min_addr, max_addr
        
        return (
            address,
            min_addr_approx if min_addr is None else min_addr,
            max_addr_approx if max_addr is None else max_addr
        )
    
    def _store(self, page_address: int, page_index: BV, value: BV, condition: Bool=None):
        assert page_address in self.pages
        assert value.size == 8
        
        value = value.simplify()
        self.pages[page_address] = self.pages[page_address].store(page_index, value, condition)
    
    def store(self, address, value: BV, endness='big'):
        if isinstance(address, int):
            address = BVV(address, self.state.arch.bits())
        assert address.size == self.bits

        for f in self.store_hooks:
            f(address, value.size)

        address, min_addr, max_addr = self._handle_symbolic_address(address, value.size, "store")

        conditions     = list()
        size           = value.size
        assert size % 8 == 0
        for i in range(size // 8 - 1, -1, -1):
            if endness == 'little':
                page_address, page_index = split_bv(address + i, self.index_bits)
            else:
                page_address, page_index = split_bv(address + size // 8 - i - 1, self.index_bits)

            if not symbolic(page_address) or not self.state.solver.symbolic(page_address):  # syntactic check + check with path constraint
                if symbolic(page_address):
                    page_address = self.state.solver.evaluate(page_address)
                page_address = page_address.value
                if page_address not in self.pages:
                    self.state.executor.put_in_errored(
                        self.state, "write unmapped"
                    )
                    return ErrorInstruction.UNMAPPED_WRITE
                self._store(page_address, page_index, value.Extract(8*(i+1)-1, 8*i))
            else: # symbolic access
                conditions   = list()
                for p in self.pages:  # can be improved?
                    at_least_one_page = False
                    if p < (min_addr >> self.index_bits) or p > (max_addr >> self.index_bits):
                        continue
                    if self.state.solver.satisfiable(extra_constraints=[
                        page_address == p
                    ]):
                        at_least_one_page = True
                        condition = p == page_address
                        conditions.append(condition)
                        self._store(p, page_index, value.Extract(8*(i+1)-1, 8*i), condition)
                if not at_least_one_page:
                    self.state.executor.put_in_errored(
                        self.state, "write unmapped"
                    )
                    return ErrorInstruction.UNMAPPED_WRITE
            if conditions:
                check_unmapped = self.state.executor.bncache.get_setting("memory.check_unmapped") == 'true'
                if check_unmapped and self.state.solver.satisfiable(extra_constraints=[
                    Or(*conditions).Not()
                ]):
                    errored_state = self.state.copy()
                    errored_state.solver.add_constraints(Or(*conditions).Not())
                    self.state.executor.put_in_errored(
                        errored_state, "write unmapped"
                    )
                self.state.solver.add_constraints(Or(*conditions))

    def _load(self, page_address: int, page_index: BV):
        assert page_address in self.pages
        return self.pages[page_address].load(page_index)
    
    def load(self, address, size: int, endness='big'):
        if isinstance(address, int):
            address = BVV(address, self.state.arch.bits())
        assert address.size == self.bits

        for f in self.load_hooks:
            f(address, size)

        address, min_addr, max_addr = self._handle_symbolic_address(address, size, "load")

        res = None
        conditions = list()
        ran = range(size - 1, -1, -1) if endness == 'little' else range(size)
        for i in ran:
            page_address, page_index = split_bv(address + i, self.index_bits)
            if not symbolic(page_address) or not self.state.solver.symbolic(page_address):  # syntactic check + check with path constraint
                if symbolic(page_address):
                    page_address = self.state.solver.evaluate(page_address)
                page_address = page_address.value
                if page_address not in self.pages:
                    self.state.executor.put_in_errored(
                        self.state, "read unmapped"
                    )
                    return ErrorInstruction.UNMAPPED_READ
                tmp = self._load(page_address, page_index)
            else: # symbolic access
                conditions = list()
                tmp = None
                for p in self.pages:  # can be improved?
                    if p < (min_addr >> self.index_bits) or p > (max_addr >> self.index_bits):
                        continue
                    if self.state.solver.satisfiable(extra_constraints=[
                        page_address == p
                    ]):
                        condition = p == page_address
                        conditions.append(condition)
                        tmp = ITE(condition,
                                self._load(p, page_index),
                                tmp
                        ) if tmp is not None else self._load(p, page_index)
                
                if tmp is None:
                    self.state.executor.put_in_errored(
                        self.state, "read unmapped"
                    )
                    return ErrorInstruction.UNMAPPED_READ
            res = tmp if res is None else res.Concat(tmp)

        if conditions:
            check_unmapped = self.state.executor.bncache.get_setting("memory.check_unmapped") == 'true'
            if check_unmapped and self.state.solver.satisfiable(extra_constraints=[
                Or(*conditions).Not()
            ]):
                errored_state = self.state.copy()
                errored_state.solver.add_constraints(Or(*conditions).Not())
                self.state.executor.put_in_errored(
                    errored_state, "read unmapped"
                )
            self.state.solver.add_constraints(Or(*conditions))

        assert res is not None
        assert res.size // 8 == size

        return res.simplify()

    def get_unmapped(self, size: int, start_from: int=None, from_end: int=True):
        start_from = start_from >> self.index_bits if start_from is not None else None
        last_page  = 2**(self.bits - self.index_bits) - 4
        first_page = 2

        if from_end:
            res   = last_page if start_from is None else start_from
            count = 0

            while res >= first_page:
                if res not in self.pages:
                    count += 1
                    if count == size:
                        return res
                else:
                    count = 0
                res -= 1
            
            return -1

        else:
            idx   = first_page if start_from is None else start_from
            res   = first_page if start_from is None else start_from
            count = 0

            while idx <= last_page:
                if idx not in self.pages:
                    count += 1
                    if count == size:
                        return res
                else:
                    count = 0
                    idx += count+1
                    res = idx

            return -1
    
    def allocate(self, size: int, init: InitData=None):
        assert size > 0
        num_pages = (size + self.page_size - 1) >> self.index_bits
        page_addr = self.get_unmapped(num_pages)
        full_addr = page_addr << self.index_bits
        self.mmap(full_addr, num_pages * self.page_size, init)
        
        return full_addr
    
    def copy(self, state):
        new_memory = Memory(state, self.page_size, self.bits)
        new_pages  = dict()
        for page_addr in self.pages:
            new_pages[page_addr] = self.pages[page_addr].copy()
        new_memory.pages = new_pages
        return new_memory
    
    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, Memory)
        for page_addr in other.pages:
            other_page = other.pages[page_addr]

            if (
                page_addr in self.pages and 
                self.pages[page_addr].mo.bvarray.z3obj.eq(other_page.mo.bvarray.z3obj)
            ):
                continue  # very same page. No need to update
            
            if page_addr not in self.pages:
                self.mmap(page_addr, self.page_size)

            self.pages[page_addr].mo.merge(
                other_page.mo,
                merge_condition
            )

    def register_read_hook(self, function):
        self.read_hooks.append(function)

    def register_store_hook(self, function):
        self.store_hooks.append(function)
