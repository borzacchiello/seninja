from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
######################################
# htonl
######################################

class htonl(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, to_convert):
        if self.state.arch.memory_endness == "Iend_LE":
            return to_convert[31:0].reversed.zero_extend(len(to_convert) - 32)
        else:
            return to_convert
