from binaryninja import SymbolType
from os_models.linux import Linuxi386, Linuxia64, LinuxArmV7
from os_models.windows import Windows

_function_cache = {}
def get_function(view, address):
    if address in _function_cache:
        return _function_cache[address]
    funcs = view.get_functions_at(address)
    if len(funcs) == 0:
        address = view.get_previous_function_start_before(address)
        funcs = view.get_functions_at(address)

    if len(funcs) > 1:
        print("WARNING: more than one function at {addr:x}".format(
            addr = address
        ))

    _function_cache[address] = funcs[0]
    return funcs[0]

def get_imported_functions_and_addresses(view):
    res_functions = dict()
    res_addresses = dict()

    symbols = view.symbols
    for name in symbols:
        symb_types = symbols[name]
        if not isinstance(symb_types, list):
            symb_types = [symb_types]
        
        for symb_type in symb_types:
            if symb_type.type == SymbolType.ImportedFunctionSymbol:
                res_functions[symb_type.address] = symb_type.name
            if symb_type.type == SymbolType.ImportAddressSymbol:
                res_addresses[symb_type.address] = symb_type.name

                if "@IAT" in symb_type.name:
                    addr = int.from_bytes(
                                view.read(symb_type.address, view.arch.address_size), 
                                'little' if view.arch.endianness.name == 'LittleEndian' else 'big'
                            )
                    res_functions[addr] = symb_type.name.replace("@IAT", "")
    
    return res_functions, res_addresses

# def get_imported_functions(view):
#     res = dict()

#     symbols = view.symbols
#     for name in symbols:
#         symb_types = symbols[name]
#         if not isinstance(symb_types, list):
#             symb_types = [symb_types]
        
#         for symb_type in symb_types:
#             if symb_type.type == SymbolType.ImportedFunctionSymbol:
#                 res[symb_type.address] = symb_type.name
    
#     return res

# def get_imported_addresses(view):
#     res = dict()

#     symbols = view.symbols
#     for name in symbols:
#         symb_types = symbols[name]
#         if not isinstance(symb_types, list):
#             symb_types = [symb_types]
        
#         for symb_type in symb_types:
#             if symb_type.type == SymbolType.ImportAddressSymbol:
#                 res[symb_type.address] = symb_type.name
#                 assert "@" in symb_type.name  # it always happen?
#                 res[
#                     int.from_bytes(
#                         view.read(symb_type.address, view.arch.address_size), 
#                         'little' if view.arch.endianness.name == 'LittleEndian' else 'big')
#                 ] = symb_type.name[:symb_type.name.find("@")]
    
#     return res

def get_addr_next_inst(view, addr):
    return addr + view.get_instruction_length(addr)

_disasm_cache = {}
def get_disasm_from_addr(view, addr):
    if addr in _disasm_cache:
        return _disasm_cache[addr]
    
    func = get_function(view, addr)
    res = view.get_disassembly(addr, func.arch)
    _disasm_cache[addr] = res
    return res

def parse_disasm_str(disasm_str):
    inst_name  = disasm_str.split(" ")[0]
    parameters = ''.join(disasm_str.split(" ")[1:]).split(",")
    return inst_name, parameters

def find_os(view):
    platform_name = view.platform.name

    if platform_name == 'linux-x86_64':
        return Linuxia64()
    elif platform_name == 'linux-x86':
        return Linuxi386()
    elif platform_name == 'linux-armv7':
        return LinuxArmV7()
    elif platform_name == 'windows-x86':
        return Windows()
    elif platform_name == 'windows-x86_64':
        return Windows()
    
    raise Exception("Unsupported os")
