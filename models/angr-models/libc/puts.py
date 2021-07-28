from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# puts
######################################

class puts(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, string):

        stdout = self.state.posix.get_fd(1)
        if stdout is None:
            return -1

        strlen = SIM_PROCEDURES['libc']['strlen']
        length = self.inline_call(strlen, string).ret_expr
        out = stdout.write(string, length)
        stdout.write_data(self.state.solver.BVV(b'\n'))
        return out + 1
