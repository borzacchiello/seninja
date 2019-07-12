from copy import deepcopy
from os_models.os_abstract import Os

class Linux(Os):
    SYSCALL_TABLE = None
    SYSCALL_PARAMS = None

    def __init__(self):
        raise NotImplementedError  # do not instantiate this class

    def get_syscall_by_number(self, n: int):
        if n not in Linuxi386.SYSCALL_TABLE:
            return None
        return self.SYSCALL_TABLE[n]

    def get_syscall_parameter(self, k: int):
        assert 0 < k <= 6
        return self.SYSCALL_PARAMS[k-1]

class Linuxi386(Linux):
    SYSCALL_TABLE = {
        0: None,
        1: None,
        2: None,
        3: None
    }
    SYSCALL_PARAMS = [
        "ebx",   "ecx",   "edx",   "esi",   "edi",   "ebp"
    ]

    def __init__(self):
        self.stdin  = []  # todo something better
        self.stdout = []  # todo something better

    def get_syscall_n_reg(self):
        return "eax"

    def get_out_syscall_reg(self):
        return "eax"

    def get_stdin(self):
        return self.stdin

    def get_stdout(self):
        return self.stdout

    def copy(self):
        res = Linuxi386()
        res.stdin = deepcopy(self.stdin)
        res.stdout = deepcopy(self.stdout)
        return res

class Linuxia64(Linux):
    SYSCALL_TABLE = {
        0: None,
        1: None,
        2: None
    }
    SYSCALL_PARAMS = [
        "rdi",	"rsi",	"rdx",	"r10",	"r8",	"r9"
    ]

    def __init__(self):
        self.stdin  = []  # todo something better
        self.stdout = []  # todo something better

    def get_syscall_n_reg(self):
        return "rax"

    def get_out_syscall_reg(self):
        return "rax"

    def get_stdin(self):
        return self.stdin

    def get_stdout(self):
        return self.stdout

    def copy(self):
        res = Linuxia64()
        res.stdin = deepcopy(self.stdin)
        res.stdout = deepcopy(self.stdout)
        return res
