from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class EncodePointer(FakeSimProcedure):
    def run(self, ptr):
        return ptr
