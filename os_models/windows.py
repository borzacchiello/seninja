from copy import deepcopy
from ..expr import Bool
from .os_file import OsFileHandler

class Windows(OsFileHandler):
    def __init__(self):
        super().__init__()
        self.stdin_fd = self.open("__stdin", "r--")
        self.stdout_fd = self.open("__stdout", "-w-")

    def get_syscall_by_number(self, n):
        raise NotImplementedError

    def get_syscall_n_reg(self):
        raise NotImplementedError

    def get_syscall_parameter(self, k):
        raise NotImplementedError

    def get_out_syscall_reg(self):
        raise NotImplementedError

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

    def copy(self):
        res = Windows()
        super().copy_to(res)
        return res

    def merge(self, other, merge_condition: Bool):
        assert isinstance(other, Windows)
        pass  # TODO implement this
