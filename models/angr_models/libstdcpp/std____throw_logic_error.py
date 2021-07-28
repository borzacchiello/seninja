from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# std::throw_logic_error
######################################

class std____throw_logic_error(FakeSimProcedure): #pylint:disable=redefined-builtin
    #pylint:disable=arguments-differ

    NO_RET = True
    ALT_NAMES = ('std::__throw_logic_error(char const*)', )

    def run(self, error):  # pylint:disable=unused-argument
        # FIXME: we need the concept of C++ exceptions to implement this right
        self.exit(1)
