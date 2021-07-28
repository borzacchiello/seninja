from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# perror
######################################

class perror(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, string):
        write = SIM_PROCEDURES['posix']['write']
        strlen = SIM_PROCEDURES['libc']['strlen']

        length = self.inline_call(strlen, string).ret_expr
        self.inline_call(write, 2, string, length)
