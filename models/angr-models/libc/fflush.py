from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

import logging
l = logging.getLogger(name=__name__)

class fflush(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument

    def run(self, fd):
        return self.state.solver.BVV(0, self.state.arch.bits)

fflush_unlocked = fflush
