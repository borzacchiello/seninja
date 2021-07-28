from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# Caller
######################################


class Caller(FakeSimProcedure):
    """
    Caller stub. Creates a Ijk_Call exit to the specified function
    """

    def run(self, target_addr=None, target_cc=None):
        self.call(target_addr, [ ], 'after_call', cc=target_cc)

    def after_call(self, target_addr=None, target_cc=None):
        pass
