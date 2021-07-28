from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# write
######################################

class write(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, fd, src, length):
        simfd = self.state.posix.get_fd(fd)
        if simfd is None:
            return -1

        return simfd.write(src, length)
