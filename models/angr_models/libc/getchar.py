from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# getchar
######################################

class getchar(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        fgetc = SIM_PROCEDURES['libc']['fgetc']
        stdin = self.state.posix.get_fd(0)
        data = self.inline_call(fgetc, 0, simfd=stdin).ret_expr
        return data

getchar_unlocked = getchar
