from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# setsockopt
######################################

class setsockopt(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, sockfd, level, optname, optval, optmain):
        return 0
