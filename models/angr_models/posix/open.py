from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# open
######################################

class open(FakeSimProcedure): #pylint:disable=W0622
    #pylint:disable=arguments-differ,unused-argument

    def run(self, p_addr, flags, mode):
        strlen = SIM_PROCEDURES['libc']['strlen']

        p_strlen = self.inline_call(strlen, p_addr)
        p_expr = self.state.memory.load(p_addr, p_strlen.max_null_index, endness='Iend_BE')
        path = self.state.solver.eval(p_expr, cast_to=bytes)

        fd = self.state.posix.open(path, flags)
        if fd is None:
            return -1
        return fd
