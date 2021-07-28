from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# getpass
######################################

class getpass(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, prompt):
        # write out the prompt
        self.inline_call(SIM_PROCEDURES['libc']['puts'], prompt)

        # malloc a buffer
        buf = self.inline_call(SIM_PROCEDURES['libc']['malloc'], 1024).ret_expr

        # read into the buffer
        self.inline_call(SIM_PROCEDURES['posix']['read'], 0, buf, 1024)

        # return the buffer
        return buf
