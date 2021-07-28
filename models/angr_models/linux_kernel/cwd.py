from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
import logging

l = logging.getLogger(name=__name__)

class getcwd(FakeSimProcedure):
    def run(self, buf, size):
        cwd = self.state.fs.cwd
        size = self.state.solver.If(size-1 > len(cwd), len(cwd), size-1)
        try:
            self.state.memory.store(buf, cwd, size=size)
            self.state.memory.store(buf + size, b'\0')
        except angr.errors.SimSegfaultException:
            return 0
        else:
            return buf

class chdir(FakeSimProcedure):
    def run(self, buf):
        cwd = self.state.mem[buf].string.concrete
        l.info('chdir(%r)', cwd)
        self.state.fs.cwd = cwd
        return 0
