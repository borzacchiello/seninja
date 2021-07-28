from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# Path terminator
######################################


class PathTerminator(FakeSimProcedure):
    NO_RET = True

    def run(self):
        return
