from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# putchar
######################################

class putchar(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, string):
        stdout = self.state.posix.get_fd(1)
        if stdout is None:
            return -1
        stdout.write_data(string[7:0])
        return string & 0xff
