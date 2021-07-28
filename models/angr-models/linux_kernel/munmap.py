from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class munmap(FakeSimProcedure):

    def run(self, addr, length): #pylint:disable=arguments-differ,unused-argument
        # TODO: actually do something
        return self.state.solver.BVV(0, self.state.arch.bits)
