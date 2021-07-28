from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class CreateMutexA(FakeSimProcedure):
    def run(self, lpMutexAttributes, bInitialOwner, lpName):
        return 1

class CreateMutexEx(CreateMutexA):
    pass