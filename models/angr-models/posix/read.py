from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# read
######################################

class read(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, fd, dst, length):
        simfd = self.state.posix.get_fd(fd)
        if simfd is None:
            return -1

        return simfd.read(dst, length)
