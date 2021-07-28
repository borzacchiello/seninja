from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# getgid
######################################

class getgid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
