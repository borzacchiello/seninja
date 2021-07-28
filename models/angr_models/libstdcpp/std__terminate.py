from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# std::terminate
######################################

class std__terminate(FakeSimProcedure): #pylint:disable=redefined-builtin
    #pylint:disable=arguments-differ

    NO_RET = True
    ALT_NAMES = ('std::terminate()', )

    def run(self):
        # FIXME: Call terminate handlers
        self.exit(1)
