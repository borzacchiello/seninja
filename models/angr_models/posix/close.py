from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# close
######################################

class close(FakeSimProcedure):
    def run(self, fd):  # pylint:disable=arguments-differ
        if self.state.posix.close(fd):
            return 0
        else:
            return -1
