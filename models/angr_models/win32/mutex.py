from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class CreateMutexA(FakeSimProcedure):
    def run(self, lpMutexAttributes, bInitialOwner, lpName):
        return 1

class CreateMutexEx(CreateMutexA):
    pass