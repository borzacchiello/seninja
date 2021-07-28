from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class gettid(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self):
        return self.state.posix.pid
