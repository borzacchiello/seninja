from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES


class setbuf(FakeSimProcedure):
    #pylint:disable=arguments-differ, unused-argument

    def run(self, stream, buf):
        return
