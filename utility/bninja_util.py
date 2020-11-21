from binaryninja import SymbolType
from .exceptions import UnsupportedOs
from ..os_models.linux import Linuxi386, Linuxia64, LinuxArmV7
from ..os_models.windows import Windows


def get_function(view, address):
    funcs = view.get_functions_at(address)
    if len(funcs) == 0:
        address = view.get_previous_function_start_before(address)
        funcs = view.get_functions_at(address)

    if len(funcs) > 1:
        print("WARNING: more than one function at {addr:x}".format(
            addr=address
        ))

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

                if "@IAT" in symb_type.name or "@GOT" in symb_type.name:
                    addr = int.from_bytes(
                        view.read(symb_type.address, view.arch.address_size),
                        'little' if view.arch.endianness.name == 'LittleEndian' else 'big'
                    )
                    res_functions[addr] = symb_type.name.replace(
                        "@IAT" if "@IAT" in symb_type.name else "@GOT", "")

    return res_functions, res_addresses


def get_addr_next_inst(view, addr):
    return addr + view.get_instruction_length(addr)


def parse_disasm_str(disasm_str):
    inst_name = disasm_str.split(" ")[0]
    parameters = ''.join(disasm_str.split(" ")[1:]).split(",")
    return inst_name, parameters


def get_address_after_merge(view, address):
    func = get_function(view, address)
    llil = func.llil.get_instruction_start(address, func.arch)
    return func.llil[llil].address


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

    raise UnsupportedOs(platform_name)
