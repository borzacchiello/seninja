from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

from cle.backends.externs.simdata.io_file import io_file_data_for_arch

######################################
# fclose
######################################

class fclose(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, fd_p):
        # Resolve file descriptor
        fd_offset = io_file_data_for_arch(self.state.arch)['fd']
        fileno = self.state.mem[fd_p + fd_offset:].int.resolved

        # TODO: use a procedure that's not a linux syscall
        sys_close = SIM_PROCEDURES['posix']['close']

        # Call system close and return
        retval = self.inline_call(sys_close, fileno).ret_expr

        return retval
