from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

######################################
# Redirect the control flow to some other places
######################################

class Redirect(FakeSimProcedure):
    #pylint:disable=arguments-differ

    NO_RET = True

    def run(self, redirect_to=None):
        if redirect_to is None:
            raise Exception("Please specify where you wanna jump to.")

        self._custom_name = "Redirect to 0x%08x" % redirect_to
        # There is definitely no refs
        self.add_successor(self.state, redirect_to, self.state.solver.true, 'Ijk_Boring')
