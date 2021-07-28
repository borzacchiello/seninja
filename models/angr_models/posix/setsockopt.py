from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# setsockopt
######################################

class setsockopt(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, sockfd, level, optname, optval, optmain):
        return 0
