from copy import deepcopy
from os_models.os_abstract import Os
import z3

class Windows(Os):
    def __init__(self):
        self.devices = {
            0: [],  # stdin
            1: []   # stdout
        }

    def get_syscall_by_number(self, n):
        raise NotImplementedError

    def get_syscall_n_reg(self):
        raise NotImplementedError

    def get_syscall_parameter(self, k):
        raise NotImplementedError

    def get_out_syscall_reg(self):
        raise NotImplementedError

    def open(self, fd: int):
        self.devices[fd] = []
    
    def is_open(self, fd: int):
        return fd in self.devices

    def close(self, fd: int):
        del self.devices[fd]
    
    def get_device_by_fd(self, fd: int):
        return self.devices[fd]

    def get_stdin(self):
        return self.devices[0]

    def get_stdout(self):
        return self.devices[1]

    def copy(self):
        res = Windows()
        res.devices = deepcopy(self.devices)
        return res

    def merge(self, other, merge_condition: z3.BoolRef):
        assert isinstance(other, Windows)
        pass  # TODO implement this