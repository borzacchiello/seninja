from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

import logging
l = logging.getLogger(name=__name__)


class atoi(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, s):
        strtol = SIM_PROCEDURES['libc']['strtol']
        return strtol.strtol_inner(s, self.state, self.state.memory, 10, True)[1]
