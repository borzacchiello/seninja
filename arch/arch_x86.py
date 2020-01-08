import z3

from .arch_abstract import Arch
from .arch_x86_sph import ArchX86SPH

class x86Arch(Arch):
    REGS = {
        'eax': { 
            'addr': 0,  
            'size': 4, 
            'sub': {
                'ax':  { 'offset': 2,  'size': 2  },
                'al':  { 'offset': 3,  'size': 1  },
                'ah':  { 'offset': 2,  'size': 1  }
            }
        },  
        'ebx': { 
            'addr': 4,  
            'size': 4,
            'sub': {
                'bx':  { 'offset': 2, 'size': 2  },
                'bl':  { 'offset': 3, 'size': 1  },
                'bh':  { 'offset': 2, 'size': 1  }
            }
        },
        'ecx': { 
            'addr': 8, 
            'size': 4,
            'sub': {
                'cx':  { 'offset': 2, 'size': 2  },
                'cl':  { 'offset': 3, 'size': 1  },
                'ch':  { 'offset': 2, 'size': 1  }
            }
        },
        'edx': { 
            'addr': 12, 
            'size': 4,
            'sub': {
                'dx':  { 'offset': 2, 'size': 2  },
                'dl':  { 'offset': 3, 'size': 1  },
                'dh':  { 'offset': 2, 'size': 1  }
            }
        },
        'esi': { 
            'addr': 16, 
            'size': 4,
            'sub': {
                'si':  { 'offset': 2, 'size': 2  },
                'sil': { 'offset': 3, 'size': 1  },
            }
        },
        'edi': { 
            'addr': 20, 
            'size': 4,
            'sub': {
                'di':  { 'offset': 2, 'size': 2  },
                'dil': { 'offset': 3, 'size': 1  }
            }
        },
        'ebp': { 
            'addr': 24, 
            'size': 4,
            'sub': {
                'bp':  { 'offset': 2, 'size': 2  },
                'bpl': { 'offset': 3, 'size': 1  }
            }
        },
        'esp': { 
            'addr': 28, 
            'size': 4,
            'sub': {
                'sp':  { 'offset': 2, 'size': 2  },
                'spl': { 'offset': 3, 'size': 1  }
            }
        },
        'eip': { 
            'addr': 32, 
            'size': 4,
            'sub': {
                'ip':  { 'offset': 2, 'size': 2  }
            }
        },
        'eflags': {
            'addr': 36,
            'size': 4,
            'sub': {
                'flags':  { 'offset': 2, 'size': 2 }
            }
        },
        'mmx0': {
            'addr': 40,
            'size': 8,
            'sub': {}
        },
        'mmx1': {
            'addr': 48,
            'size': 8,
            'sub': {}
        },
        'mmx2': {
            'addr': 56,
            'size': 8,
            'sub': {}
        },
        'mmx3': {
            'addr': 64,
            'size': 8,
            'sub': {}
        },
        'mmx4': {
            'addr': 72,
            'size': 8,
            'sub': {}
        },
        'mmx5': {
            'addr': 80,
            'size': 8,
            'sub': {}
        },
        'mmx6': {
            'addr': 88,
            'size': 8,
            'sub': {}
        },
        'mmx7': {
            'addr': 96,
            'size': 8,
            'sub': {}
        }
    }

    FLAGS = { 'c': 0, 'p': 2, 'a': 4, 'z': 6, 's': 7, 'd': 10, 'o': 11, 'c0': 32, 'c1': 33, 'c2': 34, 'c3': 35 }
    
    FLAGS_CONDS = {
        'E':   lambda s: s.regs.flags['z'] == 0,
        'NE':  lambda s: s.regs.flags['z'] == 1,
        'NEG': lambda s: s.regs.flags['s'] == 1,
        'POS': lambda s: s.regs.flags['s'] == 0,
        'O':   lambda s: s.regs.flags['o'] == 1,
        'NO':  lambda s: s.regs.flags['o'] == 0,
        'SGE': lambda s: s.regs.flags['s'] == s.regs.flags['o'],
        'SGT': lambda s: z3.And(
            s.regs.flags['z'] == 0, 
            s.regs.flags['s'] == s.regs.flags['o']),
        'SLE': lambda s: z3.And(
            s.regs.flags['z'] == 1, 
            s.regs.flags['s'] != s.regs.flags['o']),
        'SLT': lambda s: s.regs.flags['s'] != s.regs.flags['o'],
        'UGE': lambda s: s.regs.flags['c'] == 0,
        'UGT': lambda s: z3.And(
            s.regs.flags['c'] == 0, 
            s.regs.flags['z'] == 0),
        'ULE': lambda s: z3.Or(
            s.regs.flags['z'] == 1, 
            s.regs.flags['c'] == 1),
        'ULT': lambda s: s.regs.flags['c'] == 1
    }

    sph = ArchX86SPH()

    def __init__(self):
        self._bits = 32

    def bits(self):
        return self._bits

    def regs_data(self):
        return x86Arch.REGS
    
    def flags_data(self):
        return x86Arch.FLAGS
    
    def flags_default(self, flag):
        if flag == 'd':
            return 0
        return None

    def endness(self):
        return 'little'

    def getip_reg(self):
        return 'eip'

    def get_base_pointer_reg(self):
        return 'ebp'

    def get_stack_pointer_reg(self):
        return 'esp'

    def get_argument_regs(self, calling_convention):
        assert calling_convention == 'cdecl'
        return []

    def get_result_reg(self, calling_convention, size):
        if size == 8:
            return 'al'
        elif size == 16:
            return 'ax'
        elif size == 32:
            return 'eax'
        else:
            raise Exception("Wrong size in get_result_reg")

    def get_flag_cond_lambda(self, cond: str):
        assert cond in x86Arch.FLAGS_CONDS
        return x86Arch.FLAGS_CONDS[cond]

    def execute_special_handler(self, disasm_str, sv):
        res = x86Arch.sph.handle_instruction(disasm_str, sv)
        return res
