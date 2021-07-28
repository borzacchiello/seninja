from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# Path terminator
######################################


class PathTerminator(FakeSimProcedure):
    NO_RET = True

    def run(self):
        return
