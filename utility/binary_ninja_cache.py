from utility.bninja_util import (
    get_function
)

class BNCache(object):
    def __init__(self, bv):
        self.bv = bv
        self.addr_to_func_cache    = dict()
        self.name_to_func_cache    = dict()
        self.func_name_cache       = dict()
        self.llil_cache            = dict()
        self.llil_addr_cache       = dict()
        self.addr_cache            = dict()
        self.disasm_cache          = dict()
        self.instruction_len_cache = dict()

    def get_function(self, address):
        if address in self.addr_to_func_cache:
            return self.addr_to_func_cache[address]
        function = get_function(self.bv, address)
        self.addr_to_func_cache[address] = function
        return function
    
    def get_function_name(self, address):
        if address in self.func_name_cache:
            return self.func_name_cache[address]
        function = self.get_function(address)
        function_name = function.name
        self.func_name_cache[address]          = function_name
        self.name_to_func_cache[function_name] = function
        return function_name

    def get_llil(self, func_name, llil_addr):
        if (func_name, llil_addr) in self.llil_cache:
            return self.llil_cache[
                (func_name, llil_addr)
            ]
        func = self.name_to_func_cache[func_name]
        expr = func.llil[llil_addr]
        self.llil_cache[
            (func_name, llil_addr)
        ] = expr
        return expr
    
    def get_llil_address(self, func_name, address):
        if (func_name, address) in self.llil_addr_cache:
            return self.llil_addr_cache[
                (func_name, address)
            ]
        func = self.name_to_func_cache[func_name]
        llil_addr = func.llil.get_instruction_start(address, func.arch)
        self.llil_addr_cache[
            (func_name, address)
        ] = llil_addr
        return llil_addr
    
    def get_address(self, func_name, llil_addr):
        if (func_name, llil_addr) in self.addr_cache:
            return self.addr_cache[
                (func_name, llil_addr)
            ]
        addr = self.get_llil(func_name, llil_addr).address
        self.addr_cache[
            (func_name, llil_addr)
        ] = addr
        return addr

    def get_disasm(self, address):
        if address in self.disasm_cache:
            return self.disasm_cache[address]
        func = self.get_function(address)
        disasm = self.bv.get_disassembly(address, func.arch)
        self.disasm_cache[address] = disasm
        return disasm

    def get_instruction_len(self, address):
        if address in self.instruction_len_cache:
            return self.instruction_len_cache[address]
        
        ret_len = self.bv.get_instruction_length(address)
        self.instruction_len_cache[address] = ret_len
        return ret_len
