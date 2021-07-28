from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

from cle.backends.externs.simdata.io_file import io_file_data_for_arch

######################################
# fputc
######################################

class feof(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, file_ptr):
        # TODO handle errors
        fd_offset = io_file_data_for_arch(self.state.arch)['fd']
        fileno = self.state.mem[file_ptr + fd_offset:].int.concrete
        simfd = self.state.posix.get_fd(fileno)
        if simfd is None:
            return None
        return self.state.solver.If(simfd.eof(), self.state.solver.BVV(1, self.state.arch.bits), 0)

feof_unlocked = feof
