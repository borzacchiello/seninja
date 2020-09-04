class Arch(object):  # abstract class
    REGS = None

    def __init__(self):
        raise NotImplementedError

    def bits(self):
        raise NotImplementedError

    def regs_data(self):
        raise NotImplementedError

    def reg_names(self):
        raise NotImplementedError

    def flags_data(self):
        raise NotImplementedError

    def flags_default(self, flag):
        raise NotImplementedError

    def endness(self):
        raise NotImplementedError

    def save_return_address(self, state, return_address):
        raise NotImplementedError

    def get_return_address(self, state):
        raise NotImplementedError

    def getip_reg(self):
        raise NotImplementedError

    def get_base_pointer_reg(self):
        raise NotImplementedError

    def get_stack_pointer_reg(self):
        raise NotImplementedError

    def get_argument_regs(self, calling_convention):
        raise NotImplementedError

    def save_result_value(self, state, calling_convention, value):
        raise NotImplementedError

    def get_flag_cond_lambda(self, cond: str):
        raise NotImplementedError

    def execute_special_handler(self, disasm_str, sv):
        raise NotImplementedError

    @staticmethod
    def fix_reg_addressess(obj):
        assert obj.REGS is not None

        curr_addr = 0
        for reg in obj.REGS:
            if 'addr' in obj.REGS[reg]:
                # already done
                break
            obj.REGS[reg]['addr'] = curr_addr
            curr_addr += obj.REGS[reg]['size']


class SpecialInstructionHandler(object):
    def __init__(self):
        raise NotImplementedError  # do not instantiate this class

    def handle_instruction(self, disasm_str: str, sv):
        inst_name = disasm_str.split(" ")[0]
        parameters = ''.join(disasm_str.split(" ")[1:]).split(",")

        handle_name = "{}_handler".format(inst_name)
        if hasattr(self, handle_name):
            return getattr(self, handle_name)(sv, parameters)
        return False
