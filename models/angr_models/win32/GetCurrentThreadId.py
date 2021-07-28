from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class GetCurrentThreadId(FakeSimProcedure):
    def run(self):
        return 0xbad76ead
