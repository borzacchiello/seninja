from arch.arch_abstract import Arch

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
        }
    }

    FLAGS = { 'c': 0, 'p': 2, 'a': 4, 'z': 6, 's': 7, 'd': 10, 'o': 11, 'c0': 32, 'c1': 33, 'c2': 34, 'c3': 35 }

    def __init__(self):
        self._bits = 64

    def bits(self):
        return self._bits

    def regs_data(self):
        return x8664Arch.REGS
    
    def flags_data(self):
        return x8664Arch.FLAGS

    def endness(self):
        return 'little'

    def getip_reg(self):
        return 'rip'

    def get_base_pointer_reg(self):
        return 'rbp'

    def get_stack_pointer_reg(self):
        return 'rsp'
