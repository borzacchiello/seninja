from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# std::__throw_bad_cast
######################################

class std____throw_bad_cast(FakeSimProcedure): #pylint:disable=redefined-builtin
    #pylint:disable=arguments-differ

    NO_RET = True
    ALT_NAMES = ('std::__throw_bad_cast()', )

    def run(self):
        # FIXME: we need the concept of C++ exceptions to implement this right
        self.exit(1)
