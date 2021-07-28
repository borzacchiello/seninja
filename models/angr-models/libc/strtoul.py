from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class strtoul(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, nptr, endptr, base):
        strtol = SIM_PROCEDURES['libc']['strtol']
        result = self.inline_call(strtol, nptr, endptr, base).ret_expr
        return result
        