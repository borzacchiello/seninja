from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES
import logging

l = logging.getLogger(name=__name__)

class strnlen(FakeSimProcedure):
    def run(self, s, n, wchar=False): #pylint:disable=arguments-differ,unused-argument
        strlen = SIM_PROCEDURES['libc']['strlen']

        maxlen = self.state.solver.eval_one(n)
        length = self.inline_call(strlen, s, maxlen=maxlen).ret_expr
        return length
