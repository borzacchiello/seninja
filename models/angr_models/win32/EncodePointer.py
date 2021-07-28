from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class EncodePointer(FakeSimProcedure):
    def run(self, ptr):
        return ptr
