from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES
import itertools

######################################
# malloc
######################################

malloc_mem_counter = itertools.count()

class malloc(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, sim_size):
        return self.state.heap._malloc(sim_size)
