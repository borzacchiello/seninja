from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class GetCurrentProcessId(FakeSimProcedure):
    def run(self):
        return 0x1337BEE2
