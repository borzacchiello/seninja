from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

class inet_ntoa(FakeSimProcedure):
    #pylint:disable=arguments-differ,unused-argument

    def run(self, addr_in):
        # arg types: struct....... :(
        #TODO: return an IP address string
        ret_expr = self.state.solver.Unconstrained("inet_ntoa_ret", self.state.arch.bits)
        return ret_expr
