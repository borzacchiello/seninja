from enum import Enum
from ...expr import BVV, BVS


class FakeOptions(Enum):
    CGC_NON_BLOCKING_FDS = 0
    CGC_ENFORCE_FD = 1
    SYMBOL_FILL_UNCONSTRAINED_MEMORY = 2
    SYMBOL_FILL_UNCONSTRAINED_REGISTERS = 3
    USE_SYSTEM_TIMES = 4


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
        if isinstance(thing, bytes):
            return BVV(int.from_bytes(thing, 'little'), len(thing) * 8)
        assert size is not None
        assert isinstance(thing, int)
        return BVV(thing, size)

    def BVS(name, size):
        raise NotImplementedError
