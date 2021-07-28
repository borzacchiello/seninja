from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# realloc
######################################

class realloc(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, ptr, size):
        return self.state.heap._realloc(ptr, size)
