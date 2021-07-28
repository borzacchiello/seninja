from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
import logging

l = logging.getLogger('angr.procedures.win32.gethostbyname')

class gethostbyname(FakeSimProcedure):

    def run(self, _): #pylint:disable=arguments-differ
        ret_expr = self.state.solver.BVS('gethostbyname_retval', 32, key=('api', 'gethostbyname_retval'))
        return ret_expr
