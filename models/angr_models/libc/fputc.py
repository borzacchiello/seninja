from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

from cle.backends.externs.simdata.io_file import io_file_data_for_arch

######################################
# fputc
######################################

class fputc(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, c, file_ptr):
        fd_offset = io_file_data_for_arch(self.state.arch)['fd']
        fileno = self.state.mem[file_ptr + fd_offset:].int.resolved
        simfd = self.state.posix.get_fd(fileno)
        if simfd is None:
            return -1

        simfd.write_data(c[7:0])
        return c & 0xff

putc = fputc
fputc_unlocked = fputc
putc_unlocked = fputc
