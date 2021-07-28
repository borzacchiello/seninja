from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class InitializeCriticalSectionAndSpinCount(FakeSimProcedure):
    def run(self, lpCriticalSection, dwSpinCount):
        return 1

class InitializeCriticalSectionEx(FakeSimProcedure):
    def run(self, lpCriticalSection, dwSpinCount, Flags):
        return 1
