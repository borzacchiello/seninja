from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class tolower(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self, c):
        return self.state.solver.If(
            self.state.solver.And(c >= 65, c <= 90),  # A - Z
            c + 32, c)
