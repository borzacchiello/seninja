from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class fork(FakeSimProcedure):
    def run(self):
        return self.state.solver.If(self.state.solver.BoolS('fork_parent'),
                self.state.solver.BVV(1338, self.state.arch.bits),
                self.state.solver.BVV(0, self.state.arch.bits))
