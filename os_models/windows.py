from copy import deepcopy
from os_models.os_abstract import Os

class Windows(Os):
    def __init__(self):
        self.stdin  = []
        self.stdout = []

    def get_syscall_by_number(self, n):
        raise NotImplementedError

    def get_syscall_n_reg(self):
        raise NotImplementedError

    def get_syscall_parameter(self, k):
        raise NotImplementedError

    def get_out_syscall_reg(self):
        raise NotImplementedError

    def get_stdin(self):
        return self.stdin

    def get_stdout(self):
        return self.stdout

    def copy(self):
        res = Windows()
        res.stdin = deepcopy(self.stdin)
        res.stdout = deepcopy(self.stdout)
        return res
