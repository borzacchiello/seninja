from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# Unresolvable Jump Target
######################################


class UnresolvableJumpTarget(FakeSimProcedure):
    NO_RET = True

    def run(self):#pylint: disable=arguments-differ
        return
