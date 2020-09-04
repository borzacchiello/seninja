from ..expr import And, Or
from .arch_abstract import Arch
from .arch_x86_64_sph import ArchX8664SPH


class x8664Arch(Arch):
    REGS = {
        'rax': {
            'size': 8,
            'sub': {
                'eax': {'offset': 4,  'size': 4},
                'ax':  {'offset': 6,  'size': 2},
                'al':  {'offset': 7,  'size': 1},
                'ah':  {'offset': 6,  'size': 1}
            }
        },
        'rbx': {
            'size': 8,
            'sub': {
                'ebx': {'offset': 4, 'size': 4},
                'bx':  {'offset': 6, 'size': 2},
                'bl':  {'offset': 7, 'size': 1},
                'bh':  {'offset': 6, 'size': 1}
            }
        },
        'rcx': {
            'size': 8,
            'sub': {
                'ecx': {'offset': 4, 'size': 4},
                'cx':  {'offset': 6, 'size': 2},
                'cl':  {'offset': 7, 'size': 1},
                'ch':  {'offset': 6, 'size': 1}
            }
        },
        'rdx': {
            'size': 8,
            'sub': {
                'edx': {'offset': 4, 'size': 4},
                'dx':  {'offset': 6, 'size': 2},
                'dl':  {'offset': 7, 'size': 1},
                'dh':  {'offset': 6, 'size': 1}
            }
        },
        'rsi': {
            'size': 8,
            'sub': {
                'esi': {'offset': 4, 'size': 4},
                'si':  {'offset': 6, 'size': 2},
                'sil': {'offset': 7, 'size': 1},
            }
        },
        'rdi': {
            'size': 8,
            'sub': {
                'edi': {'offset': 4, 'size': 4},
                'di':  {'offset': 6, 'size': 2},
                'dil': {'offset': 7, 'size': 1}
            }
        },
        'rbp': {
            'size': 8,
            'sub': {
                'ebp': {'offset': 4, 'size': 4},
                'bp':  {'offset': 6, 'size': 2},
                'bpl': {'offset': 7, 'size': 1}
            }
        },
        'rsp': {
            'size': 8,
            'sub': {
                'esp': {'offset': 4, 'size': 4},
                'sp':  {'offset': 6, 'size': 2},
                'spl': {'offset': 7, 'size': 1}
            }
        },
        'rip': {
            'size': 8,
            'sub': {
                'eip': {'offset': 4, 'size': 4},
                'ip':  {'offset': 6, 'size': 2},
            }
        },
        'rflags': {
            'size': 8,
            'sub': {
                'eflags': {'offset': 4, 'size': 4},
                'flags':  {'offset': 6, 'size': 2}
            }
        },
        'fsbase': {
            'size': 8,
            'sub': {}
        },
        'gsbase': {
            'size': 8,
            'sub': {}
        },
        'r8': {
            'size': 8,
            'sub': {
                'r8d': {'offset': 4, 'size': 4},
                'r8w': {'offset': 6, 'size': 2},
                'r8b': {'offset': 7, 'size': 1}
            }
        },
        'r9': {
            'size': 8,
            'sub': {
                'r9d': {'offset': 4, 'size': 4},
                'r9w': {'offset': 6, 'size': 2},
                'r9b': {'offset': 7, 'size': 1}
            }
        },
        'r10': {
            'size': 8,
            'sub': {
                'r10d': {'offset': 4, 'size': 4},
                'r10w': {'offset': 6, 'size': 2},
                'r10b': {'offset': 7, 'size': 1}
            }
        },
        'r11': {
            'size': 8,
            'sub': {
                'r11d': {'offset': 4, 'size': 4},
                'r11w': {'offset': 6, 'size': 2},
                'r11b': {'offset': 7, 'size': 1}
            }
        },
        'r12': {
            'size': 8,
            'sub': {
                'r12d': {'offset': 4, 'size': 4},
                'r12w': {'offset': 6, 'size': 2},
                'r12b': {'offset': 7, 'size': 1}
            }
        },
        'r13': {
            'size': 8,
            'sub': {
                'r13d': {'offset': 4, 'size': 4},
                'r13w': {'offset': 6, 'size': 2},
                'r13b': {'offset': 7, 'size': 1}
            }
        },
        'r14': {
            'size': 8,
            'sub': {
                'r14d': {'offset': 4, 'size': 4},
                'r14w': {'offset': 6, 'size': 2},
                'r14b': {'offset': 7, 'size': 1}
            }
        },
        'r15': {
            'size': 8,
            'sub': {
                'r15d': {'offset': 4, 'size': 4},
                'r15w': {'offset': 6, 'size': 2},
                'r15b': {'offset': 7, 'size': 1}
            }
        },
        'zmm0': {
            'size': 64,
            'sub': {
                'ymm0': {'offset': 32, 'size': 32},
                'xmm0': {'offset': 48, 'size': 16}
            }
        },
        'zmm1': {
            'size': 64,
            'sub': {
                'ymm1': {'offset': 32, 'size': 32},
                'xmm1': {'offset': 48, 'size': 16}
            }
        },
        'zmm2': {
            'size': 64,
            'sub': {
                'ymm2': {'offset': 32, 'size': 32},
                'xmm2': {'offset': 48, 'size': 16}
            }
        },
        'zmm3': {
            'size': 64,
            'sub': {
                'ymm3': {'offset': 32, 'size': 32},
                'xmm3': {'offset': 48, 'size': 16}
            }
        },
        'zmm4': {
            'size': 64,
            'sub': {
                'ymm4': {'offset': 32, 'size': 32},
                'xmm4': {'offset': 48, 'size': 16}
            }
        },
        'zmm5': {
            'size': 64,
            'sub': {
                'ymm5': {'offset': 32, 'size': 32},
                'xmm5': {'offset': 48, 'size': 16}
            }
        },
        'zmm6': {
            'size': 64,
            'sub': {
                'ymm6': {'offset': 32, 'size': 32},
                'xmm6': {'offset': 48, 'size': 16}
            }
        },
        'zmm7': {
            'size': 64,
            'sub': {
                'ymm7': {'offset': 32, 'size': 32},
                'xmm7': {'offset': 48, 'size': 16}
            }
        },
        'zmm8': {
            'size': 64,
            'sub': {
                'ymm8': {'offset': 32, 'size': 32},
                'xmm8': {'offset': 48, 'size': 16}
            }
        },
        'zmm9': {
            'size': 64,
            'sub': {
                'ymm9': {'offset': 32, 'size': 32},
                'xmm9': {'offset': 48, 'size': 16}
            }
        },
        'zmm10': {
            'size': 64,
            'sub': {
                'ymm10': {'offset': 32, 'size': 32},
                'xmm10': {'offset': 48, 'size': 16}
            }
        },
        'zmm11': {
            'size': 64,
            'sub': {
                'ymm11': {'offset': 32, 'size': 32},
                'xmm11': {'offset': 48, 'size': 16}
            }
        },
        'zmm12': {
            'size': 64,
            'sub': {
                'ymm12': {'offset': 32, 'size': 32},
                'xmm12': {'offset': 48, 'size': 16}
            }
        },
        'zmm13': {
            'size': 64,
            'sub': {
                'ymm13': {'offset': 32, 'size': 32},
                'xmm13': {'offset': 48, 'size': 16}
            }
        },
        'zmm14': {
            'size': 64,
            'sub': {
                'ymm14': {'offset': 32, 'size': 32},
                'xmm14': {'offset': 48, 'size': 16}
            }
        },
        'zmm15': {
            'size': 64,
            'sub': {
                'ymm15': {'offset': 32, 'size': 32},
                'xmm15': {'offset': 48, 'size': 16}
            }
        },
        'zmm16': {
            'size': 64,
            'sub': {
                'ymm16': {'offset': 32, 'size': 32},
                'xmm16': {'offset': 48, 'size': 16}
            }
        },
        'zmm17': {
            'size': 64,
            'sub': {
                'ymm17': {'offset': 32, 'size': 32},
                'xmm17': {'offset': 48, 'size': 16}
            }
        },
        'zmm18': {
            'size': 64,
            'sub': {
                'ymm18': {'offset': 32, 'size': 32},
                'xmm18': {'offset': 48, 'size': 16}
            }
        },
        'zmm19': {
            'size': 64,
            'sub': {
                'ymm19': {'offset': 32, 'size': 32},
                'xmm19': {'offset': 48, 'size': 16}
            }
        },
        'zmm20': {
            'size': 64,
            'sub': {
                'ymm20': {'offset': 32, 'size': 32},
                'xmm20': {'offset': 48, 'size': 16}
            }
        },
        'zmm21': {
            'size': 64,
            'sub': {
                'ymm21': {'offset': 32, 'size': 32},
                'xmm21': {'offset': 48, 'size': 16}
            }
        },
        'zmm22': {
            'size': 64,
            'sub': {
                'ymm22': {'offset': 32, 'size': 32},
                'xmm22': {'offset': 48, 'size': 16}
            }
        },
        'zmm23': {
            'size': 64,
            'sub': {
                'ymm23': {'offset': 32, 'size': 32},
                'xmm23': {'offset': 48, 'size': 16}
            }
        },
        'zmm24': {
            'size': 64,
            'sub': {
                'ymm24': {'offset': 32, 'size': 32},
                'xmm24': {'offset': 48, 'size': 16}
            }
        },
        'zmm25': {
            'size': 64,
            'sub': {
                'ymm25': {'offset': 32, 'size': 32},
                'xmm25': {'offset': 48, 'size': 16}
            }
        },
        'zmm26': {
            'size': 64,
            'sub': {
                'ymm26': {'offset': 32, 'size': 32},
                'xmm26': {'offset': 48, 'size': 16}
            }
        },
        'zmm27': {
            'size': 64,
            'sub': {
                'ymm27': {'offset': 32, 'size': 32},
                'xmm27': {'offset': 48, 'size': 16}
            }
        },
        'zmm28': {
            'size': 64,
            'sub': {
                'ymm28': {'offset': 32, 'size': 32},
                'xmm28': {'offset': 48, 'size': 16}
            }
        },
        'zmm29': {
            'size': 64,
            'sub': {
                'ymm29': {'offset': 32, 'size': 32},
                'xmm29': {'offset': 48, 'size': 16}
            }
        },
        'zmm30': {
            'size': 64,
            'sub': {
                'ymm30': {'offset': 32, 'size': 32},
                'xmm30': {'offset': 48, 'size': 16}
            }
        },
        'zmm31': {
            'size': 64,
            'sub': {
                'ymm31': {'offset': 32, 'size': 32},
                'xmm31': {'offset': 48, 'size': 16}
            }
        }
    }

    FLAGS = {'c': 0, 'p': 2, 'a': 4, 'z': 6, 's': 7, 'd': 10,
             'o': 11, 'c0': 32, 'c1': 33, 'c2': 34, 'c3': 35}

    REG_NAMES = [
        "rip", "rsp", "rbp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
        "r14", "r15", "zmm0", "zmm1", "zmm2",
        "zmm3", "zmm4", "zmm5", "zmm6", "zmm7", "zmm8", "zmm9", "zmm10", "zmm11", "zmm12", "zmm13", "zmm14",
        "zmm15", "zmm16", "zmm17", "zmm18", "zmm19", "zmm20", "zmm21", "zmm22", "zmm23", "zmm24", "zmm25",
        "zmm26", "zmm27", "zmm28", "zmm29", "zmm30", "zmm31"
    ]

    FLAGS_CONDS = {
        'E': lambda s: s.regs.flags['z'] == 0,
        'NE': lambda s: s.regs.flags['z'] == 1,
        'NEG': lambda s: s.regs.flags['s'] == 1,
        'POS': lambda s: s.regs.flags['s'] == 0,
        'O': lambda s: s.regs.flags['o'] == 1,
        'NO': lambda s: s.regs.flags['o'] == 0,
        'SGE': lambda s: s.regs.flags['s'] == s.regs.flags['o'],
        'SGT': lambda s: And(
            s.regs.flags['z'] == 0,
            s.regs.flags['s'] == s.regs.flags['o']),
        'SLE': lambda s: And(
            s.regs.flags['z'] == 1,
            s.regs.flags['s'] != s.regs.flags['o']),
        'SLT': lambda s: s.regs.flags['s'] != s.regs.flags['o'],
        'UGE': lambda s: s.regs.flags['c'] == 0,
        'UGT': lambda s: And(
            s.regs.flags['c'] == 0,
            s.regs.flags['z'] == 0),
        'ULE': lambda s: Or(
            s.regs.flags['z'] == 1,
            s.regs.flags['c'] == 1),
        'ULT': lambda s: s.regs.flags['c'] == 1
    }

    sph = ArchX8664SPH()

    def __init__(self):
        self._bits = 64

    def bits(self):
        return self._bits

    def regs_data(self):
        return x8664Arch.REGS

    def reg_names(self):
        return x8664Arch.REG_NAMES

    def flags_data(self):
        return x8664Arch.FLAGS

    def flags_default(self, flag):
        if flag == 'd':
            return 0
        return None

    def endness(self):
        return 'little'

    def getip_reg(self):
        return 'rip'

    def get_base_pointer_reg(self):
        return 'rbp'

    def get_stack_pointer_reg(self):
        return 'rsp'

    def save_return_address(self, state, return_address):
        state.stack_push(return_address)

    def get_return_address(self, state):
        return state.stack_pop()

    def get_argument_regs(self, calling_convention):
        if calling_convention == 'cdecl':
            return []
        elif calling_convention == 'sysv':
            return ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
        elif calling_convention == 'win64':
            return ['rcx', 'rdx', 'r8', 'r9']
        raise Exception("Unknown calling convention {name}".format(
            name=calling_convention
        ))

    def save_result_value(self, state, calling_convention, value):
        if value.size == 8:
            state.regs.al = value
        elif value.size == 16:
            state.regs.ax = value
        elif value.size == 32:
            state.regs.rax = value.ZeroExt(32)
        elif value.size == 64:
            state.regs.rax = value
        else:
            raise Exception("Wrong size in save_result_value")

    def get_flag_cond_lambda(self, cond: str, state):
        assert cond in x8664Arch.FLAGS_CONDS
        return x8664Arch.FLAGS_CONDS[cond]

    def execute_special_handler(self, disasm_str, sv):
        res = x8664Arch.sph.handle_instruction(disasm_str, sv)
        return res


Arch.fix_reg_addressess(x8664Arch)
