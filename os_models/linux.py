from copy import deepcopy
from os_models.os_abstract import Os
import models.linux_syscalls as models
from expr import Bool

class Linux(Os):
    SYSCALL_TABLE = None
    SYSCALL_PARAMS = None

    def __init__(self):
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