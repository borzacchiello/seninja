from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class sleep(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument
    def run(self, seconds):
        return 0
