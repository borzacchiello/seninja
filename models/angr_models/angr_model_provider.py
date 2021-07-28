# A compatibility layer between the angr models and SENinja models
from inspect import signature
from .procedures_dict import SIM_PROCEDURES
from . import claripy
from ...expr import ITECases, BV, BVV, Bool, BoolV
from ...utility.models_util import get_arg_k
from ...utility.expr_wrap_util import symbolic


class FakeCGC(object):
    EBADF = 1
    EFAULT = 2
    EINVAL = 3
    ENOMEM = 4
    ENOSYS = 5
    EPIPE = 6

    FD_SETSIZE = 1024
    max_allocation = 0x100000

    def __init__(self, seninja_state):
        self.seninja_state = seninja_state
        self.allocation_base = 0xb8000000

    def addr_invalid(self, a):
        # print("addr_invalid(", a, ") ?", a == 0)
        return a == 0

    def get_max_sinkhole(self, length):
        if length > FakeCGC.max_allocation:
            length = FakeCGC.max_allocation
        res = self.seninja_state.mem.allocate(length)
        return res


class FakeArch(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state

    @property
    def bits(self):
        return self.seninja_state.arch.bits()

    @property
    def bytes(self):
        return self.seninja_state.arch.bits() // 8


class FakeSolver(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state

    def symbolic(self, v):
        return symbolic(v)

    def max_int(self, v):
        return self.seninja_state.solver.max(v)

    def ite_cases(self, cases, default):
        return claripy.ite_cases(cases, default)

    def BVV(self, thing, size=None):
        return claripy.BVV(thing, size)

    def And(self, *args):
        return claripy.And(*args)

    def If(self, cond, iftrue, iffalse):
        return claripy.If(cond, iftrue, iffalse)


class FakeMemory(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state

    def store(self, addr, value, size, condition, endness):
        # print("FakeMemory.store(", addr, ",", value, ",", size, ",", condition, ",", endness, ")")
        if isinstance(value, int):
            value = BVV(value, size * 8)
        self.seninja_state.mem.store(
            addr, value, endness="little" if endness == "Iend_LE" else "big", store_condition=condition
        )

class FakeState(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state
        self.fake_mem = FakeMemory(seninja_state)
        self.fake_solver = FakeSolver(seninja_state)
        self.fake_arch = FakeArch(seninja_state)
        self.cgc = FakeCGC(seninja_state)

    @property
    def memory(self):
        return self.fake_mem

    @property
    def solver(self):
        return self.fake_solver

    @property
    def arch(self):
        return self.fake_arch

    @property
    def mem(self):
        raise NotImplementedError


class AngrModelProvider(object):
    def __init__(self):
        self.angr_models = dict()
        self.angr_models["win"] = dict()
        self.angr_models["linux"] = dict()
        self.angr_models["cgc"] = dict()

        # Let's focus on CGC models...
        for name in SIM_PROCEDURES["cgc"]:
            if name == "FakeSimProcedure":
                continue
            self.angr_models["cgc"][name] = SIM_PROCEDURES["cgc"][name]

    def get_implemented_models(self, os_name):
        if os_name not in self.angr_models:
            return list()
        return self.angr_models[os_name].keys()

    def get_model(self, os_name, fun_name):
        if os_name not in self.angr_models:
            return None
        if fun_name not in self.angr_models[os_name]:
            return None

        def make_condom(model_calss):
            c = model_calss()
            num_args = len(signature(c.run).parameters)

            def f(seninja_state, view):
                state = FakeState(seninja_state)
                c.set_state(state)
                args = list()
                for i in range(num_args):
                    args.append(
                        get_arg_k(seninja_state, i+1, seninja_state.arch.bits() // 8, view))

                # print(signature(c.run))
                # print("running", model_calss, "with arguments:", args)
                return c.run(*args)
            return f

        return make_condom(self.angr_models[os_name][fun_name])
