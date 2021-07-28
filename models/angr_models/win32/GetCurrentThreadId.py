from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class GetCurrentThreadId(FakeSimProcedure):
    def run(self):
        return 0xbad76ead
