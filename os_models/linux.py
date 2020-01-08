from copy import deepcopy
from ..models import linux_syscalls as models
from ..expr import Bool
from .os_abstract import Os

class Linux(Os):
    SYSCALL_TABLE  = {}
    SYSCALL_PARAMS = {}

    def __init__(self):
        self.devices = []
        raise NotImplementedError  # do not instantiate this class

    def get_syscall_by_number(self, n: int):
        if n not in self.SYSCALL_TABLE:
            return None
        return self.SYSCALL_TABLE[n]

    def get_syscall_parameter(self, k: int):
        assert 0 < k <= 6
        return self.SYSCALL_PARAMS[k-1]

    def get_stdin(self):
        return self.devices[0]

    def get_stdout(self):
        return self.devices[1]
    
    def open(self, fd: int):
        self.devices[fd] = []
    
    def is_open(self, fd: int):
        return fd in self.devices

    def close(self, fd: int):
        del self.devices[fd]
    
    def get_device_by_fd(self, fd: int):
        return self.devices[fd]

class Linuxi386(Linux):
    SYSCALL_TABLE = {
        0: None,
        3: models.read_handler,
        4: models.write_handler
    }
    SYSCALL_PARAMS = [
        "ebx",   "ecx",   "edx",   "esi",   "edi",   "ebp"
    ]

    def __init__(self):
        self.devices = {
            0: [],
            1: []
        }  # todo something better

    def get_syscall_n_reg(self):
        return "eax"

    def get_out_syscall_reg(self):
        return "eax"

    def copy(self):
        res = Linuxi386()
        res.devices = deepcopy(self.devices)
        return res
    
    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, Linuxi386)
        pass  # TODO implement this

class Linuxia64(Linux):
    SYSCALL_TABLE = {
        0: models.read_handler,
        1: models.write_handler,
        2: None
    }
    SYSCALL_PARAMS = [
        "rdi",	"rsi",	"rdx",	"r10",	"r8",	"r9"
    ]

    def __init__(self):
        self.devices = {
            0: [],
            1: []
        }  # todo something better

    def get_syscall_n_reg(self):
        return "rax"

    def get_out_syscall_reg(self):
        return "rax"

    def copy(self):
        res = Linuxia64()
        res.devices = deepcopy(self.devices)
        return res

    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, Linuxia64)
        pass  # TODO implement this

class LinuxArmV7(Linux):

    SYSCALL_TABLE = {
        0x900003: models.read_handler,
        0x900004: models.write_handler
    }
    SYSCALL_PARAMS = [
        "r0", "r1", "r2", "r3", "r4", "r5", "r6"
    ]

    def __init__(self):
        self.devices = {
            0: [],
            1: []
        }  # todo something better

    def get_syscall_n_reg(self):
        return "r7"

    def get_out_syscall_reg(self):
        return "r0"

    def copy(self):
        res = LinuxArmV7()
        res.devices = deepcopy(self.devices)
        return res

    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, LinuxArmV7)
        pass  # TODO implement this
