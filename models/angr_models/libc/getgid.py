from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# getgid
######################################

class getgid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
