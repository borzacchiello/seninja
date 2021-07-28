from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class gettid(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self):
        return self.state.posix.pid
