from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

# these are NOT suitable for multibyte characters
class CharNextA(FakeSimProcedure):
    def run(self, ptr):
        return self.state.solver.If(self.state.mem[ptr].uint8_t.resolved == 0, ptr, ptr + 1)

class CharPrevA(FakeSimProcedure):
    def run(self, start, ptr):
        return self.state.solver.If(start == ptr, start, ptr - 1)
