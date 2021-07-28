from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class InterlockedExchange(FakeSimProcedure):

    def run(self, target, value): #pylint:disable=arguments-differ
        if not self.state.solver.symbolic(target):
            old_value = self.state.memory.load(target, 4, endness=self.state.arch.memory_endness)
            self.state.memory.store(target, value)
        else:
            old_value = self.state.solver.Unconstrained("unconstrained_ret_%s" % self.display_name, self.state.arch.bits, key=('api', 'InterlockedExchange'))

        return old_value
