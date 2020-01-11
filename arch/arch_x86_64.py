from ..expr import And, Or
from .arch_abstract import Arch
from .arch_x86_64_sph import ArchX8664SPH

class x8664Arch(Arch):
    REGS = {
        'rax': { 
            'addr': 0,  
            'size': 8, 
            'sub': {
                'eax': { 'offset': 4,  'size': 4  },
                'ax':  { 'offset': 6,  'size': 2  },
                'al':  { 'offset': 7,  'size': 1  },
                'ah':  { 'offset': 6,  'size': 1  }
            }
        },  
        'rbx': { 
            'addr': 8,  
            'size': 8,
            'sub': {
                'ebx': { 'offset': 4, 'size': 4  },
                'bx':  { 'offset': 6, 'size': 2  },
                'bl':  { 'offset': 7, 'size': 1  },
                'bh':  { 'offset': 6, 'size': 1  }
            }
        },
        'rcx': { 
            'addr': 16, 
            'size': 8,
            'sub': {
                'ecx': { 'offset': 4, 'size': 4  },
                'cx':  { 'offset': 6, 'size': 2  },
                'cl':  { 'offset': 7, 'size': 1  },
                'ch':  { 'offset': 6, 'size': 1  }
            }
        },
        'rdx': { 
            'addr': 24, 
            'size': 8,
            'sub': {
                'edx': { 'offset': 4, 'size': 4  },
                'dx':  { 'offset': 6, 'size': 2  },
                'dl':  { 'offset': 7, 'size': 1  },
                'dh':  { 'offset': 6, 'size': 1  }
            }
        },
        'rsi': { 
            'addr': 32, 
            'size': 8,
            'sub': {
                'esi': { 'offset': 4, 'size': 4  },
                'si':  { 'offset': 6, 'size': 2  },
                'sil': { 'offset': 7, 'size': 1  },
            }
        },
        'rdi': { 
            'addr': 40, 
            'size': 8,
            'sub': {
                'edi': { 'offset': 4, 'size': 4  },
                'di':  { 'offset': 6, 'size': 2  },
                'dil': { 'offset': 7, 'size': 1  }
            }
        },
        'rbp': { 
            'addr': 48, 
            'size': 8,
            'sub': {
                'ebp': { 'offset': 4, 'size': 4  },
                'bp':  { 'offset': 6, 'size': 2  },
                'bpl': { 'offset': 7, 'size': 1  }
            }
        },
        'rsp': { 
            'addr': 56, 
            'size': 8,
            'sub': {
                'esp': { 'offset': 4, 'size': 4  },
                'sp':  { 'offset': 6, 'size': 2  },
                'spl': { 'offset': 7, 'size': 1  }
            }
        },
        'rip': { 
            'addr': 64, 
            'size': 8,
            'sub': {
                'eip': { 'offset': 4, 'size': 4  },
                'ip':  { 'offset': 6, 'size': 2  },
            }
        },
        'rflags': {
            'addr': 72,
            'size': 8,
            'sub': {
                'eflags': { 'offset': 4, 'size': 4 },
                'flags':  { 'offset': 6, 'size': 2 }
            }
        },
        'fs': {
            'addr': 80,
            'size': 8,
            'sub': {}
        },
        'gs': {
            'addr': 88,
            'size': 8,
            'sub': {}
        },
        'r8': {
            'addr': 96,
            'size': 8,
            'sub': {
                'r8d': { 'offset': 4, 'size': 4  },
                'r8w': { 'offset': 6, 'size': 2  },
                'r8b': { 'offset': 7, 'size': 1  }
            }
        },
        'r9': {
            'addr': 104,
            'size': 8,
            'sub': {
                'r9d': { 'offset': 4, 'size': 4  },
                'r9w': { 'offset': 6, 'size': 2  },
                'r9b': { 'offset': 7, 'size': 1  }
            }
        },
        'r10': {
            'addr': 112,
            'size': 8,
            'sub': {
                'r10d': { 'offset': 4, 'size': 4  },
                'r10w': { 'offset': 6, 'size': 2  },
                'r10b': { 'offset': 7, 'size': 1  }
            }
        },
        'r11': {
            'addr': 120,
            'size': 8,
            'sub': {
                'r11d': { 'offset': 4, 'size': 4  },
                'r11w': { 'offset': 6, 'size': 2  },
                'r11b': { 'offset': 7, 'size': 1  }
            }
        },
        'r12': {
            'addr': 128,
            'size': 8,
            'sub': {
                'r12d': { 'offset': 4, 'size': 4  },
                'r12w': { 'offset': 6, 'size': 2  },
                'r12b': { 'offset': 7, 'size': 1  }
            }
        },
        'r13': {
            'addr': 136,
            'size': 8,
            'sub': {
                'r13d': { 'offset': 4, 'size': 4  },
                'r13w': { 'offset': 6, 'size': 2  },
                'r13b': { 'offset': 7, 'size': 1  }
            }
        },
        'r14': {
            'addr': 144,
            'size': 8,
            'sub': {
                'r14d': { 'offset': 4, 'size': 4  },
                'r14w': { 'offset': 6, 'size': 2  },
                'r14b': { 'offset': 7, 'size': 1  }
            }
        },
        'r15': {
            'addr': 152,
            'size': 8,
            'sub': {
                'r15d': { 'offset': 4, 'size': 4  },
                'r15w': { 'offset': 6, 'size': 2  },
                'r15b': { 'offset': 7, 'size': 1  }
            }
        },
        'mmx0': {
            'addr': 160,
            'size': 8,
            'sub': {}
        },
        'mmx1': {
            'addr': 168,
            'size': 8,
            'sub': {}
        },
        'mmx2': {
            'addr': 176,
            'size': 8,
            'sub': {}
        },
        'mmx3': {
            'addr': 184,
            'size': 8,
            'sub': {}
        },
        'mmx4': {
            'addr': 192,
            'size': 8,
            'sub': {}
        },
        'mmx5': {
            'addr': 200,
            'size': 8,
            'sub': {}
        },
        'mmx6': {
            'addr': 208,
            'size': 8,
            'sub': {}
        },
        'mmx7': {
            'addr': 216,
            'size': 8,
            'sub': {}
        },
        'zmm0': {
            'addr': 224,
            'size': 64,
            'sub': {
                'ymm0': { 'offset': 32, 'size': 32 },
                'xmm0': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm1': {
            'addr': 288,
            'size': 64,
            'sub': {
                'ymm1': { 'offset': 32, 'size': 32 },
                'xmm1': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm2': {
            'addr': 352,
            'size': 64,
            'sub': {
                'ymm2': { 'offset': 32, 'size': 32 },
                'xmm2': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm3': {
            'addr': 416,
            'size': 64,
            'sub': {
                'ymm3': { 'offset': 32, 'size': 32 },
                'xmm3': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm4': {
            'addr': 480,
            'size': 64,
            'sub': {
                'ymm4': { 'offset': 32, 'size': 32 },
                'xmm4': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm5': {
            'addr': 544,
            'size': 64,
            'sub': {
                'ymm5': { 'offset': 32, 'size': 32 },
                'xmm5': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm6': {
            'addr': 608,
            'size': 64,
            'sub': {
                'ymm6': { 'offset': 32, 'size': 32 },
                'xmm6': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm7': {
            'addr': 672,
            'size': 64,
            'sub': {
                'ymm7': { 'offset': 32, 'size': 32 },
                'xmm7': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm8': {
            'addr': 736,
            'size': 64,
            'sub': {
                'ymm8': { 'offset': 32, 'size': 32 },
                'xmm8': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm9': {
            'addr': 800,
            'size': 64,
            'sub': {
                'ymm9': { 'offset': 32, 'size': 32 },
                'xmm9': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm10': {
            'addr': 864,
            'size': 64,
            'sub': {
                'ymm10': { 'offset': 32, 'size': 32 },
                'xmm10': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm11': {
            'addr': 928,
            'size': 64,
            'sub': {
                'ymm11': { 'offset': 32, 'size': 32 },
                'xmm11': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm12': {
            'addr': 992,
            'size': 64,
            'sub': {
                'ymm12': { 'offset': 32, 'size': 32 },
                'xmm12': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm13': {
            'addr': 1056,
            'size': 64,
            'sub': {
                'ymm13': { 'offset': 32, 'size': 32 },
                'xmm13': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm14': {
            'addr': 1120,
            'size': 64,
            'sub': {
                'ymm14': { 'offset': 32, 'size': 32 },
                'xmm14': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm15': {
            'addr': 1184,
            'size': 64,
            'sub': {
                'ymm15': { 'offset': 32, 'size': 32 },
                'xmm15': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm16': {
            'addr': 1248,
            'size': 64,
            'sub': {
                'ymm16': { 'offset': 32, 'size': 32 },
                'xmm16': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm17': {
            'addr': 1312,
            'size': 64,
            'sub': {
                'ymm17': { 'offset': 32, 'size': 32 },
                'xmm17': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm18': {
            'addr': 1376,
            'size': 64,
            'sub': {
                'ymm18': { 'offset': 32, 'size': 32 },
                'xmm18': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm19': {
            'addr': 1440,
            'size': 64,
            'sub': {
                'ymm19': { 'offset': 32, 'size': 32 },
                'xmm19': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm20': {
            'addr': 1504,
            'size': 64,
            'sub': {
                'ymm20': { 'offset': 32, 'size': 32 },
                'xmm20': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm21': {
            'addr': 1568,
            'size': 64,
            'sub': {
                'ymm21': { 'offset': 32, 'size': 32 },
                'xmm21': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm22': {
            'addr': 1632,
            'size': 64,
            'sub': {
                'ymm22': { 'offset': 32, 'size': 32 },
                'xmm22': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm23': {
            'addr': 1696,
            'size': 64,
            'sub': {
                'ymm23': { 'offset': 32, 'size': 32 },
                'xmm23': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm24': {
            'addr': 1760,
            'size': 64,
            'sub': {
                'ymm24': { 'offset': 32, 'size': 32 },
                'xmm24': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm25': {
            'addr': 1824,
            'size': 64,
            'sub': {
                'ymm25': { 'offset': 32, 'size': 32 },
                'xmm25': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm26': {
            'addr': 1888,
            'size': 64,
            'sub': {
                'ymm26': { 'offset': 32, 'size': 32 },
                'xmm26': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm27': {
            'addr': 1952,
            'size': 64,
            'sub': {
                'ymm27': { 'offset': 32, 'size': 32 },
                'xmm27': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm28': {
            'addr': 2016,
            'size': 64,
            'sub': {
                'ymm28': { 'offset': 32, 'size': 32 },
                'xmm28': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm29': {
            'addr': 2080,
            'size': 64,
            'sub': {
                'ymm29': { 'offset': 32, 'size': 32 },
                'xmm29': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm30': {
            'addr': 2144,
            'size': 64,
            'sub': {
                'ymm30': { 'offset': 32, 'size': 32 },
                'xmm30': { 'offset': 48, 'size': 16 }
            }
        },
        'zmm31': {
            'addr': 2208,
            'size': 64,
            'sub': {
                'ymm31': { 'offset': 32, 'size': 32 },
                'xmm31': { 'offset': 48, 'size': 16 }
            }
        }
    }

    FLAGS = { 'c': 0, 'p': 2, 'a': 4, 'z': 6, 's': 7, 'd': 10, 'o': 11, 'c0': 32, 'c1': 33, 'c2': 34, 'c3': 35 }

    REG_NAMES = [
        "rip", "rsp", "rbp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
        "r14", "r15", "mmx0", "mmx1", "mmx2", "mmx3", "mmx4", "mmx5", "mmx6", "mmx7", "zmm0", "zmm1", "zmm2",
        "zmm3", "zmm4", "zmm5", "zmm6", "zmm7", "zmm8", "zmm9", "zmm10", "zmm11", "zmm12", "zmm13", "zmm14",
        "zmm15", "zmm16", "zmm17", "zmm18", "zmm19", "zmm20", "zmm21", "zmm22", "zmm23", "zmm24", "zmm25",
        "zmm26", "zmm27", "zmm28", "zmm29", "zmm30", "zmm31"
    ]
    
    FLAGS_CONDS = {
        'E':   lambda s: s.regs.flags['z'] == 0,
        'NE':  lambda s: s.regs.flags['z'] == 1,
        'NEG': lambda s: s.regs.flags['s'] == 1,
        'POS': lambda s: s.regs.flags['s'] == 0,
        'O':   lambda s: s.regs.flags['o'] == 1,
        'NO':  lambda s: s.regs.flags['o'] == 0,
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

    def get_argument_regs(self, calling_convention):
        if calling_convention == 'cdecl':
            return []
        elif calling_convention == 'sysv':
            return ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9']
        elif calling_convention == 'win64':
            return ['rcx', 'rdx', 'r8', 'r9']
        raise Exception("Unknown calling convention {name}".format(
            name = calling_convention
        ))
    
    def get_result_reg(self, calling_convention, size):
        if size == 8:
            return 'al'
        elif size == 16:
            return 'ax'
        elif size == 32:
            return 'eax'
        elif size == 64:
            return 'rax'
        else:
            raise Exception("Wrong size in get_result_reg")

    def get_flag_cond_lambda(self, cond: str, state):
        assert cond in x8664Arch.FLAGS_CONDS
        return x8664Arch.FLAGS_CONDS[cond]

    def execute_special_handler(self, disasm_str, sv):
        res = x8664Arch.sph.handle_instruction(disasm_str, sv)
        return res
