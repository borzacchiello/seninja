from copy import deepcopy
from ..models import linux_syscalls as models
from ..expr import Bool
from .os_file import OsFileHandler


class Linux(OsFileHandler):
    SYSCALL_TABLE = {}
    SYSCALL_PARAMS = {}

    def __init__(self):
        super().__init__()
        self.stdin_fd = self.open("__stdin",  "r--")
        self.stdout_fd = self.open("__stdout", "-w-")

    def get_syscall_by_number(self, n: int):
        if n not in self.SYSCALL_TABLE:
            return None
        return self.SYSCALL_TABLE[n]

    def get_syscall_parameter(self, k: int):
        assert 0 < k <= 6
        return self.SYSCALL_PARAMS[k-1]

    def get_stdin_stream(self):
        session = self.descriptors_map[self.stdin_fd]
        session_idx = session.seek_idx
        session.seek(0)
        res = session.read(session.symfile.file_size)
        session.seek(session_idx)

        return res

    def get_stdout_stream(self):
        session = self.descriptors_map[self.stdout_fd]
        session_idx = session.seek_idx
        session.seek(0)
        res = session.read(session.symfile.file_size)
        session.seek(session_idx)

        return res

    def copy_to(self, other):
        super().copy_to(other)
        other.stdin_fd = self.stdin_fd
        other.stdout_fd = other.stdout_fd


class Linuxi386(Linux):
    SYSCALL_TABLE = {
        0: None,
        3: models.read_handler,
        4: models.write_handler
    }
    SYSCALL_PARAMS = [
        "ebx",   "ecx",   "edx",   "esi",   "edi",   "ebp"
    ]

    def get_syscall_n_reg(self):
        return "eax"

    def get_out_syscall_reg(self):
        return "eax"

    def copy(self):
        res = Linuxi386()
        super().copy_to(res)
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

    def get_syscall_n_reg(self):
        return "rax"

    def get_out_syscall_reg(self):
        return "rax"

    def copy(self):
        res = Linuxia64()
        super().copy_to(res)
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

    def get_syscall_n_reg(self):
        return "r7"

    def get_out_syscall_reg(self):
        return "r0"

    def copy(self):
        res = LinuxArmV7()
        super().copy_to(res)
        return res

    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, LinuxArmV7)
        pass  # TODO implement this
