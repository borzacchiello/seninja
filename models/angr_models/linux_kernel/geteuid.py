from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# geteuid
######################################


class geteuid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000

class geteuid32(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
