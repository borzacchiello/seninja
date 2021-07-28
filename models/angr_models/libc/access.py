from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# access
######################################


class access(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, path, mode):

        ret = self.state.solver.BVS('access', self.arch.bits)
        self.state.add_constraints(self.state.solver.Or(ret == 0, ret == -1))
        return ret
