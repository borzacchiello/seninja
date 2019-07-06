from arch.arch_abstract import Arch

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
        }
    }

    def __init__(self):
        self._bits = 32

    def bits(self):
        return self._bits

    def regs_data(self):
        return x86Arch.REGS

    def endness(self):
        return 'little'

    def getip_reg(self):
        return 'eip'

    def get_base_pointer_reg(self):
        return 'ebp'

    def get_stack_pointer_reg(self):
        return 'esp'
    
    def get_result_register(self, size):
        if size == 8:
            return 'al'
        elif size == 16:
            return 'ax'
        elif size == 32:
            return 'eax'
        else:
            raise Exception("invalid size")
