from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# abort
######################################

class abort(FakeSimProcedure):
    NO_RET = True

    def run(self):
        self.exit(1)
