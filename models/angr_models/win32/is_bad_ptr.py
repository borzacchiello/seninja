from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class IsBadReadPtr(FakeSimProcedure):
    def run(self, ptr, length):
        try:
            return (~self.state.memory.permissions(ptr)[0]).zero_extend(self.state.arch.bits-1)
        except angr.errors.SimMemoryError:
            return 1

class IsBadWritePtr(FakeSimProcedure):
    def run(self, ptr, length):
        try:
            return (~self.state.memory.permissions(ptr)[1]).zero_extend(self.state.arch.bits-1)
        except angr.errors.SimMemoryError:
            return 1

class IsBadCodePtr(FakeSimProcedure):
    def run(self, ptr, length):
        try:
            return (~self.state.memory.permissions(ptr)[2]).zero_extend(self.state.arch.bits-1)
        except angr.errors.SimMemoryError:
            return 1
