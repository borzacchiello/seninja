from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES
import logging

l = logging.getLogger(name=__name__)

class CallReturn(FakeSimProcedure):
    NO_RET = True

    def run(self):
        l.info("A factory.call_state-created path returned!")
        return
