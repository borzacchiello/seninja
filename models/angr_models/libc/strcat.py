from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class strcat(FakeSimProcedure):
    # pylint: disable=arguments-differ
    def run(self, dst, src):
        strlen = SIM_PROCEDURES['libc']['strlen']
        strncpy = SIM_PROCEDURES['libc']['strncpy']
        src_len = self.inline_call(strlen, src).ret_expr
        dst_len = self.inline_call(strlen, dst).ret_expr

        self.inline_call(strncpy, dst + dst_len, src, src_len+1, src_len=src_len)
        return dst
