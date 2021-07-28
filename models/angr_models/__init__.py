from ...expr import BVV, BVS
from .procedures_dict import SIM_PROCEDURES

class FakeSimProcedure(object):
    def __init__(self):
        self.state = None

    def set_state(self, state):
        self.state = state

    def inline_call(self, *args):
        raise NotImplementedError

    def exit(self, code):
        raise NotImplementedError


class FakeSimProcedureError(Exception):
    def __init__(self, msg):
        super().__init__(msg)


class claripy(object):
    def BVV(thing, size=None):
        raise NotImplementedError

    def BVS(name, size):
        raise NotImplementedError
