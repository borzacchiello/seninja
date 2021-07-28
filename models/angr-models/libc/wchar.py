from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class wcscmp(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, lpString1, lpString2):
        strcmp = SIM_PROCEDURES['libc']['strcmp']
        return self.inline_call(strcmp, lpString1, lpString2, wchar=True).ret_expr

class wcscasecmp(FakeSimProcedure):
    #pylint:disable=arguments-differ
    def run(self, lpString1, lpString2):
        strcmp = SIM_PROCEDURES['libc']['strcmp']
        return self.inline_call(strcmp, lpString1, lpString2, wchar=True, ignore_case=True).ret_expr
