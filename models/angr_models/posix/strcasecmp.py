from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class strcasecmp(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, a_addr, b_addr):
        strlen = SIM_PROCEDURES['libc']['strlen']

        a_strlen = self.inline_call(strlen, a_addr)
        b_strlen = self.inline_call(strlen, b_addr)
        maxlen = self.state.solver.BVV(max(a_strlen.max_null_index, b_strlen.max_null_index), self.state.arch.bits)

        strncmp = self.inline_call(SIM_PROCEDURES['libc']['strncmp'], a_addr, b_addr, maxlen, a_len=a_strlen, b_len=b_strlen, ignore_case=True)
        return strncmp.ret_expr
