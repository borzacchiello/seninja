from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# __vsnprintf
######################################

class vsnprintf(FakeSimProcedure):
    #pylint:disable=arguments-differ

    def run(self, str_ptr, size, fmt, ap): #pylint:disable=unused-argument
        # This function returns
        # Add another exit to the retn_addr that is at the top of the stack now
        
        if self.state.solver.eval(size) == 0:
            return size
        
        self.state.memory.store(str_ptr, b"\x00")

        return size - 1
