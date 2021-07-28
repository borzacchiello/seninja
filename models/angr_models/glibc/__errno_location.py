from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# __errno_location
######################################

class __errno_location(FakeSimProcedure):
    def run(self):  #pylint:disable=arguments-differ
        return self.state.libc.errno_location
