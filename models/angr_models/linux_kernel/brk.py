from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
import logging

l = logging.getLogger(name=__name__)

class brk(FakeSimProcedure):
    """
    This implements the brk system call.
    """

    #pylint:disable=arguments-differ

    def run(self, new_brk):
        r = self.state.posix.set_brk(new_brk)
        l.debug('brk(%s) = %s', new_brk, r)
        return r
