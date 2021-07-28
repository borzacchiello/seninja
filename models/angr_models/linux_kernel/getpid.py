from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

#pylint:disable=arguments-differ

class getpid(FakeSimProcedure):
    def run(self):
        return self.state.posix.pid


class getppid(FakeSimProcedure):
    def run(self):
        return self.state.posix.ppid
