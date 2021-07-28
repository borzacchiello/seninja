from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# listen (but not really)
######################################
import logging
l = logging.getLogger(name=__name__)

class listen(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, sockfd, backlog): #pylint:disable=unused-argument
        return self.state.solver.Unconstrained('listen', self.state.arch.bits, key=('api', 'listen'))

