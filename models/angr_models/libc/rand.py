from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class rand(FakeSimProcedure):
    def run(self):
        rval = self.state.solver.BVS('rand', 31, key=('api', 'rand'))
        return rval.zero_extend(self.state.arch.bits - 31)
