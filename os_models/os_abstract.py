class Os(object):
    # syscall
    def get_syscall_by_number(self, n):
        raise NotImplementedError

    def get_syscall_n_reg(self):
        raise NotImplementedError

    def get_syscall_parameter(self, k):
        raise NotImplementedError

    def get_out_syscall_reg(self):
        raise NotImplementedError
    # devices

    def open(self, filename, mode):
        raise NotImplementedError

    def read(self, fd, size):
        raise NotImplementedError

    def write(self, fd, data):
        raise NotImplementedError

    def is_open(self, fd: int):
        raise NotImplementedError

    def close(self, fd: int):
        raise NotImplementedError

    def get_stdin_stream(self):
        raise NotImplementedError

    def get_stdout_stream(self):
        raise NotImplementedError
    # other

    def copy(self):
        raise NotImplementedError

    def merge(self, other, merge_condition):
        raise NotImplementedError
