from .arch_abstract import Arch
from .arch_armv7_sph import ArmV7SPH


class ArmV7Arch(Arch):
    REGS = {
        'r0': {
            'size': 4,
            'sub': {}
        },
        'r1': {
            'size': 4,
            'sub': {}
        },
        'r2': {
            'size': 4,
            'sub': {}
        },
        'r3': {
            'size': 4,
            'sub': {}
        },
        'r4': {
            'size': 4,
            'sub': {}
        },
        'r5': {
            'size': 4,
            'sub': {}
        },
        'r6': {
            'size': 4,
            'sub': {}
        },
        'r7': {
            'size': 4,
            'sub': {}
        },
        'r8': {
            'size': 4,
            'sub': {}
        },
        'r9': {
            'size': 4,
            'sub': {}
        },
        'r10': {
            'size': 4,
            'sub': {}
        },
        'r11': {
            'size': 4,
            'sub': {}
        },
        'r12': {
            'size': 4,
            'sub': {}
        },
        'sp': {
            'size': 4,
            'sub': {}
        },
        'lr': {
            'size': 4,
            'sub': {}
        },
        'pc': {
            'size': 4,
            'sub': {}
        }
    }

    FLAGS = {'n': 0, 'z': 0, 'c': 0, 'v': 0, 'e': 0, 't': 0, 'm': 0, 'j': 0}

    REG_NAMES = [
        "pc", "sp", "r0", "r1", "r2",  "r3",  "r4",  "r5",
        "r6", "r7", "r8", "r9", "r10", "r11", "r12", "lr"
    ]

    FLAGS_CONDS = {}

    sph = ArmV7SPH()

    def __init__(self):
        self._bits = 32

    def bits(self):
        return self._bits

    def regs_data(self):
        return ArmV7Arch.REGS

    def reg_names(self):
        return ArmV7Arch.REG_NAMES

    def flags_data(self):
        return ArmV7Arch.FLAGS

    def flags_default(self, flag):
        return None

    def endness(self):
        # is this correct? Not always...
        return 'little'

    def getip_reg(self):
        return 'pc'

    def get_base_pointer_reg(self):
        return 'r11'

    def get_stack_pointer_reg(self):
        return 'sp'

    def save_return_address(self, state, return_address):
        state.regs.lr = return_address

    def get_return_address(self, state):
        return state.regs.lr

    def get_argument_regs(self, calling_convention):
        assert calling_convention == 'cdecl'
        return ['r0', 'r1', 'r2', 'r3']

    def save_result_value(self, state, calling_convention, value):
        if value.size == 32:
            state.regs.r0 = value
        else:
            state.regs.r0 = value.ZeroExt(32 - value.size)

    def get_flag_cond_lambda(self, cond: str, state):
        assert cond in ArmV7Arch.FLAGS_CONDS
        return ArmV7Arch.FLAGS_CONDS[cond]

    def execute_special_handler(self, disasm_str, sv):
        res = ArmV7Arch.sph.handle_instruction(disasm_str, sv)
        return res


Arch.fix_reg_addressess(ArmV7Arch)
