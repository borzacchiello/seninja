
from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# openlog
######################################

class openlog(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, ident, option, facility):
        # A stub for openlog that does not do anything yet.
        return
