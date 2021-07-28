from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# bind (but not really)
######################################
import logging
l = logging.getLogger(name=__name__)

class bind(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, fd, addr_ptr, addr_len): #pylint:disable=unused-argument
        return self.state.solver.Unconstrained('bind', self.state.arch.bits, key=('api', 'bind'))
