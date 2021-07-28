from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# geteuid
######################################

class geteuid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
