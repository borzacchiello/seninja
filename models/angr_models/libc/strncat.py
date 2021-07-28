from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
import logging

l = logging.getLogger(name=__name__)

class strncat(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, dst, src, limit):
        strncpy = SIM_PROCEDURES['libc']['strncpy']
        strlen = SIM_PROCEDURES['libc']['strlen']
        dst_len = self.inline_call(strlen, dst).ret_expr
        src_len = self.inline_call(strlen, src).ret_expr

        self.inline_call(strncpy, dst + dst_len, src, limit, src_len=src_len)

        return dst
