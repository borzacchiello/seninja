from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# calloc
######################################

class calloc(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, sim_nmemb, sim_size):
        return self.state.heap._calloc(sim_nmemb, sim_size)
