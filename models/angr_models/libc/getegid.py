from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# getegid
######################################

class getegid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
