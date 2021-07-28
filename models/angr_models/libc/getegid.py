from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# getegid
######################################

class getegid(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self):
        return 1000
