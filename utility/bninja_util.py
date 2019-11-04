from binaryninja import SymbolType
from os_models.linux import Linuxi386, Linuxia64
from os_models.windows import Windows

def get_function(view, address):
    func = view.get_function_at(address)
    if func is None:
        return view.get_function_at(view.get_previous_function_start_before(address))
    return func

def get_imported_functions(view):
    res = dict()

    symbols = view.symbols
    for name in symbols:
        symb_types = symbols[name]
        if not isinstance(symb_types, list):
            symb_types = [symb_types]
        
        for symb_type in symb_types:
            if symb_type.type == SymbolType.ImportedFunctionSymbol:
                res[symb_type.address] = symb_type.name
    
    return res

def get_imported_addresses(view):
    res = dict()

    symbols = view.symbols
    for name in symbols:
        symb_types = symbols[name]
        if not isinstance(symb_types, list):
            symb_types = [symb_types]
        
        for symb_type in symb_types:
            if symb_type.type == SymbolType.ImportAddressSymbol:
                res[symb_type.address] = symb_type.name
    
    return res

def get_addr_next_inst(view, addr):
    return addr + view.get_instruction_length(addr)

def get_disasm_from_addr(view, addr):
    bbs = view.get_basic_blocks_at(addr)
    if len(bbs) == 0:
        return ""
    if len(bbs) > 1:
        print("WARNING: aliasing of basic blocks")
        return ""
    return bbs[0].view.get_disassembly(addr)

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
    elif platform_name == 'windows-x86':
        return Windows()
    elif platform_name == 'windows-x86_64':
        return Windows()
    
    raise Exception("Unsupported os")
