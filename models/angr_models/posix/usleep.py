from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class usleep(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument
    def run(self, n):
        return 0
