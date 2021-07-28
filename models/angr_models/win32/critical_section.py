from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class InitializeCriticalSectionAndSpinCount(FakeSimProcedure):
    def run(self, lpCriticalSection, dwSpinCount):
        return 1

class InitializeCriticalSectionEx(FakeSimProcedure):
    def run(self, lpCriticalSection, dwSpinCount, Flags):
        return 1
