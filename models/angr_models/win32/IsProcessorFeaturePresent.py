from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class IsProcessorFeaturePresent(FakeSimProcedure):
    def run(self, feature): # pylint: disable=unused-argument,no-self-use,arguments-differ
        return 0 # we're dumb as shit!!!!
