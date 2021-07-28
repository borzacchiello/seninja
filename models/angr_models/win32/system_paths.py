from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class GetTempPathA(FakeSimProcedure):
    RESULT = claripy.BVV(b"C:\\Temp\\")

    def run(self, nBufferLength, lpBuffer):
        length = self.state.solver.eval_one(nBufferLength)

        copy_len = min(self.RESULT.length//8, length - 1)
        self.state.memory.store(lpBuffer, self.RESULT[self.RESULT.length - 1 : self.RESULT.length - copy_len*8].concat(claripy.BVV(0, 8)))
        return self.RESULT.length // 8

class GetWindowsDirectoryA(FakeSimProcedure):
    RESULT = claripy.BVV(b"C:\\Windows")

    def run(self, lpBuffer, uSize):
        length = self.state.solver.eval_one(uSize)

        copy_len = min(self.RESULT.length//8, length - 1)
        self.state.memory.store(lpBuffer, self.RESULT[self.RESULT.length - 1 : self.RESULT.length - copy_len*8].concat(claripy.BVV(0, 8)))
        return self.RESULT.length // 8
