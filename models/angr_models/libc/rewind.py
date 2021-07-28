from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# rewind
######################################

class rewind(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, file_ptr):
        fseek = SIM_PROCEDURES['libc']['fseek']
        self.inline_call(fseek, file_ptr, 0, 0)

        return None
