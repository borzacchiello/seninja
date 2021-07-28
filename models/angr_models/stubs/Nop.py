from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# Doing nothing
######################################


class Nop(FakeSimProcedure):
    def run(self):
        pass
