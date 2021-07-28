from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# getsockopt
######################################

class getsockopt(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, sockfd, level, optname, optval, optlen):

        # TODO: ...

        return 0
