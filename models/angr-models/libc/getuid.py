from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# getuid
######################################

class getuid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
