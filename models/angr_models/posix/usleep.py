from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class usleep(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument
    def run(self, n):
        return 0
