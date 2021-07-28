from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class setvbuf(FakeSimProcedure):
    def run(self, stream, buf, type_, size):
        return 0
