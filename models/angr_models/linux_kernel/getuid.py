from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# getuid
######################################


class getuid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000

class getuid32(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
