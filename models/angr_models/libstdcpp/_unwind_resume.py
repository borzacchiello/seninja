from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# __unwind_resume
######################################

class _Unwind_Resume(FakeSimProcedure): #pylint:disable=redefined-builtin
    #pylint:disable=arguments-differ

    NO_RET = True

    def run(self):
        pass
