from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class GetCurrentProcessId(FakeSimProcedure):
    def run(self):
        return 0x1337BEE2
