from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class srand(FakeSimProcedure):
    def run(self, seed):
        self.ret()
