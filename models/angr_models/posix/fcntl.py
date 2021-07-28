from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# fcntl
######################################

class fcntl(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, fd, cmd):
        #  this is a stupid stub that does not do anything besides returning an unconstrained variable.
        return self.state.solver.BVS('fcntl_retval', self.state.arch.bits)
