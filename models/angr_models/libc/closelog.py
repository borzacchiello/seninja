
from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# openlog
######################################

class closelog(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self):
        # A stub for closelog that does not do anything yet.
        return
