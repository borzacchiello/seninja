from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class sigaction(FakeSimProcedure):
    def run(self, signum, act, oldact): #pylint:disable=arguments-differ,unused-argument
        # TODO: actually do something
        return self.state.solver.BVV(0, self.state.arch.bits)

class rt_sigaction(FakeSimProcedure):
    def run(self, signum, act, oldact, sigsetsize): #pylint:disable=arguments-differ,unused-argument
        # TODO: actually do something
        # ...hack
        if self.state.solver.is_true(signum == 33):
            return self.state.libc.ret_errno('EINVAL')
        return self.state.solver.BVV(0, self.state.arch.bits)
