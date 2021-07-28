from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class _dl_initial_error_catch_tsd(FakeSimProcedure):
    def run(self, static_addr=0):
        return static_addr
