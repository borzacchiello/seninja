from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class ExitProcess(FakeSimProcedure):
    NO_RET = True
    def run(self, exit_status):
        self.exit(exit_status)
