from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

import logging
l = logging.getLogger(name=__name__)

class system(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument
    def run(self, cmd):
        retcode = self.state.solver.Unconstrained('system_returncode', 8, key=('api', 'system'))
        return retcode.zero_extend(self.state.arch.bits - 8)
