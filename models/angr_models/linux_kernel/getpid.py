from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

#pylint:disable=arguments-differ

class getpid(FakeSimProcedure):
    def run(self):
        return self.state.posix.pid


class getppid(FakeSimProcedure):
    def run(self):
        return self.state.posix.ppid
