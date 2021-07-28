from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES
import tempfile

######################################
# tmpnam
######################################

class tmpnam(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, tmp_file_path_addr):
        L_tmpnam = 20

        if self.state.solver.eval(tmp_file_path_addr) != 0:
            return tmp_file_path_addr

        tmp_file_path = tempfile.mktemp()
        malloc = SIM_PROCEDURES['libc']['malloc']
        addr = self.inline_call(malloc, L_tmpnam).ret_expr
        self.state.memory.store(addr,
                                tmp_file_path.encode() + b'\x00')

        return addr
