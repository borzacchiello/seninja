from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# Doing nothing
######################################


class Nop(FakeSimProcedure):
    def run(self):
        pass
