from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# __errno_location
######################################

class __errno_location(FakeSimProcedure):
    def run(self):  #pylint:disable=arguments-differ
        return self.state.libc.errno_location
