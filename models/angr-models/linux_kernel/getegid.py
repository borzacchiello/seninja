from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES
from angr.sim_type import SimTypeInt

######################################
# getegid
######################################


class getegid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        self.return_type = SimTypeInt(16, True)
        return 1000


class getegid32(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        self.return_type = SimTypeInt(32, True)
        return 1000
