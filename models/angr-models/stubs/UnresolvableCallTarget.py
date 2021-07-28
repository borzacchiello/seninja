from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# Unresolvable Call Target
######################################


class UnresolvableCallTarget(FakeSimProcedure):
    NO_RET = False

    def run(self):#pylint: disable=arguments-differ
        return
