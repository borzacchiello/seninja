from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

from cle.backends.externs.simdata.io_file import io_file_data_for_arch

######################################
# ftell
######################################

class ftell(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, file_ptr):
        fd_offset = io_file_data_for_arch(self.state.arch)['fd']
        fd = self.state.mem[file_ptr + fd_offset].int.resolved
        simfd = self.state.posix.get_fd(fd)
        if simfd is None:
            return -1
        pos = simfd.tell()
        if pos is None:
            return -1
        return pos

ftello = ftell
