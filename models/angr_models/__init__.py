from enum import Enum
from ...expr import BVV, BVS, And, Bool, BoolV, ITE, ITECases, BV


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
    # Compatibility layer with claripy

    @staticmethod
    def BVV(thing, size=None):
        if isinstance(thing, bytes):
            return BVV(int.from_bytes(thing, 'little'), len(thing) * 8)
        assert size is not None
        assert isinstance(thing, int)
        return BVV(thing, size)

    @staticmethod
    def BVS(name, size):
        raise NotImplementedError

    @staticmethod
    def And(*args):
        # print("And:", args)
        processed_args = list()
        for arg in args:
            if not isinstance(arg, Bool):
                assert isinstance(arg, bool)
                arg = BoolV(arg)
            processed_args.append(
                arg
            )

        return And(*processed_args)

    @staticmethod
    def ite_cases(cases, default):
        assert isinstance(default, BV)

        processed_cases = list()
        for cond, val in cases:
            if not isinstance(cond, Bool):
                assert isinstance(cond, bool)
                cond = BoolV(cond)
            if not isinstance(val, BV):
                assert isinstance(val, int)
                val = BVV(val, default.size)
            processed_cases.append(
                (cond, val)
            )

        # print("ite_cases(", processed_cases, ",", default, ") =", ITECases(processed_cases, default))
        return ITECases(processed_cases, default)

    @staticmethod
    def If(cond, iftrue, iffalse):
        return ITE(cond, iftrue, iffalse)
