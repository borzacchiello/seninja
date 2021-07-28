from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class GetCommandLineA(FakeSimProcedure):
    def run(self):
        return self.project.simos.acmdln_ptr

class GetCommandLineW(FakeSimProcedure):
    def run(self):
        return self.project.simos.wcmdln_ptr
