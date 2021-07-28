from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class _terminate(FakeSimProcedure): #pylint:disable=redefined-builtin
    #pylint:disable=arguments-differ

    NO_RET = True

    def run(self, exit_code): #pylint:disable=unused-argument
        return
