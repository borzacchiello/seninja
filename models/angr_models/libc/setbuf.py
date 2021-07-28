from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES


class setbuf(FakeSimProcedure):
    #pylint:disable=arguments-differ, unused-argument

    def run(self, stream, buf):
        return
