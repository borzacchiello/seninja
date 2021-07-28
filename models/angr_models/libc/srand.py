from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class srand(FakeSimProcedure):
    def run(self, seed):
        self.ret()
