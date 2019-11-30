from arch.arch_abstract import Arch
from arch.arch_armv7_sph import ArmV7SPH

class ArmV7Arch(Arch):
    REGS = {
        'r0': {
            'addr': 0,
            'size': 4,
            'sub': {}
        },
        'r1': {
            'addr': 4,
            'size': 4,
            'sub': {}
        },
        'r2': {
            'addr': 8,
            'size': 4,
            'sub': {}
        },
        'r3': {
            'addr': 12,
            'size': 4,
            'sub': {}
        },
        'r4': {
            'addr': 16,
            'size': 4,
            'sub': {}
        },
        'r5': {
            'addr': 20,
            'size': 4,
            'sub': {}
        },
        'r6': {
            'addr': 24,
            'size': 4,
            'sub': {}
        },
        'r7': {
            'addr': 28,
            'size': 4,
            'sub': {}
        },
        'r8': {
            'addr': 32,
            'size': 4,
            'sub': {}
        },
        'r9': {
            'addr': 36,
            'size': 4,
            'sub': {}
        },
        'r10': {
            'addr': 40,
            'size': 4,
            'sub': {}
        },
        'r11': {
            'addr': 44,
            'size': 4,
            'sub': {}
        },
        'r12': {
            'addr': 48,
            'size': 4,
            'sub': {}
        },
        'sp': {
            'addr': 52,
            'size': 4,
            'sub': {}
        },
        'lr': {
            'addr': 56,
            'size': 4,
            'sub': {}
        },
        'pc': {
            'addr': 60,
            'size': 4,
            'sub': {}
        }
    }

    FLAGS = {'n': 0, 'z': 0, 'c': 0, 'v': 0, 'e': 0, 't': 0, 'm': 0, 'j': 0}

    FLAGS_CONDS = {}

    sph = ArmV7SPH()

    def __init__(self):
        self._bits = 32

    def bits(self):
        return self._bits

    def regs_data(self):
        return ArmV7Arch.REGS
    
    def flags_data(self):
        return ArmV7Arch.FLAGS

    def endness(self):
        # is this correct? Not always...
        return 'little'

    def getip_reg(self):
        return 'pc'

    def get_base_pointer_reg(self):
        return 'r11'

    def get_stack_pointer_reg(self):
        return 'sp'

    def get_argument_regs(self, calling_convention):
        assert calling_convention == 'cdecl'
        return ['r0', 'r1', 'r2', 'r3']

    def get_result_reg(self, calling_convention, size):
        return 'r0'

    def get_flag_cond_lambda(self, cond: str, state):
        assert cond in ArmV7Arch.FLAGS_CONDS
        return ArmV7Arch.FLAGS_CONDS[cond]

    def execute_special_handler(self, disasm_str, sv):
        res = ArmV7Arch.sph.handle_instruction(disasm_str, sv)
        return res
