
from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# openlog
######################################

class openlog(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, ident, option, facility):
        # A stub for openlog that does not do anything yet.
        return
