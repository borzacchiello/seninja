from utility.armv7_native_handlers_util import (
    parse_mnemonic, parse_immediate, 
    parse_rot_shift, ArmV7Mnemonic,
    ArmV7RotShift
)
from arch.arch_abstract import SpecialInstructionHandler

class ArmV7SPH(SpecialInstructionHandler):
    def __init__(self):
        pass

    # override
    def handle_instruction(self, disasm_str: str, sv):
        inst_name  = disasm_str.split(" ")[0]
        parameters = ''.join(disasm_str.split(" ")[1:]).split(",")

        parsed_mnemonic = parse_mnemonic(inst_name)
        handle_name = "{}_handler".format(parsed_mnemonic.mnemonic)
        if hasattr(self, handle_name):
            return getattr(self, handle_name)(sv, parsed_mnemonic, parameters)
        return False
    
    def uxtb_handler(self, sv, parsed_mnemonic, parameters):
        dst_reg = parameters[0]
        src_reg = parameters[1]  # cannot be an immediate, right?

        src = getattr(sv.state.regs, src_reg)
        if len(parameters) == 3:
            # there is a rotation/shift
            assert False # TODO

        setattr(sv.state.regs, dst_reg, src.Extract(7, 0).ZeroExt(24))

        return True
