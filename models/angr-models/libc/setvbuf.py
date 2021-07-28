from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class setvbuf(FakeSimProcedure):
    def run(self, stream, buf, type_, size):
        return 0
