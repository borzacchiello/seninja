import z3

from copy import deepcopy
from collections import OrderedDict
from .utility.expr_wrap_util import symbolic
from .expr import BV, BVV, Bool, And, Or

USE_OPT_SOLVER = 0


class Solver(object):
    def __init__(self, state):
        self.state = state
        self.assertions = []
        self._solver = z3.Optimize() if USE_OPT_SOLVER else z3.Solver()
        self._min_cache = OrderedDict()
        self._max_cache = OrderedDict()
        self._eval_cache = OrderedDict()
        self._symb_check_cache = OrderedDict()

    def __str__(self):
        return "<SymSolver id: 0x%x, %d assertions>" % \
            (id(self), len(self.assertions))

    def __repr__(self):
        return self.__str__()

    def _invalidate_cache(self):
        self._min_cache = OrderedDict()
        self._max_cache = OrderedDict()
        self._eval_cache = OrderedDict()
        self._symb_check_cache = OrderedDict()

    def get_path_constraint(self):
        return self.assertions

    def add_constraints(self, *constraints, simplify_constraint=True):
        self._invalidate_cache()
        for c in constraints:
            assert isinstance(c, Bool)
            if simplify_constraint:
                c = c.simplify()
            cz3 = c.z3obj
            if not z3.BoolVal(True).eq(cz3):
                self._solver.add(cz3)
                self.assertions.append(c)

    def _add_tmp_constraints(self, *constraints):
        for c in constraints:
            assert isinstance(c, Bool)
            c = c.simplify()
            cz3 = c.z3obj
            if not z3.BoolVal(True).eq(cz3):
                self._solver.add(cz3)

    def satisfiable(self, extra_constraints: list = None):
        if extra_constraints:
            self._solver.push()
            self._add_tmp_constraints(*extra_constraints)

        res = self._solver.check().r == 1

        if extra_constraints:
            self._solver.pop()
        return res

    def evaluate(self, var, extra_constraints: list = None) -> int:
        if extra_constraints:
            self._solver.push()
            self._add_tmp_constraints(*extra_constraints)
        elif var in self._eval_cache:
            return self._eval_cache[var]

        if not self.satisfiable():
            if extra_constraints:
                self._solver.pop()
            assert False  # not satisfiable!
        model = self._solver.model()
        res = model.evaluate(var.z3obj, model_completion=True)
        res = BVV(res.as_long(), var.size)

        if extra_constraints:
            self._solver.pop()
        else:
            self._eval_cache[var] = res
        return res

    def evaluate_upto(self, var, n, extra_constraints: list = None) -> list:
        self._solver.push()
        if extra_constraints:
            self._add_tmp_constraints(*extra_constraints)

        if not self.satisfiable():
            if extra_constraints:
                self._solver.pop()
            assert False  # not satisfiable!
        res = list()
        while n > 0 and self.satisfiable():
            model = self._solver.model()
            r = model.evaluate(var.z3obj, model_completion=True)
            r = BVV(r.as_long(), var.size)
            res.append(r)
            self._add_tmp_constraints(var != r)
            n -= 1

        self._solver.pop()
        return res

    def symbolic(self, val: BV):
        if val in self._symb_check_cache:
            return self._symb_check_cache[val]

        res = len(self.evaluate_upto(val, 2)) != 1
        self._symb_check_cache[val] = res
        return res

    def _max_binary_search(self, val: BV):
        lb = 0
        ub = 2 ** val.size - 1
        while lb <= ub:
            m = (lb + ub) // 2
            if not self.satisfiable(extra_constraints=[val.UGE(m)]):
                ub = m - 1
            else:
                lb = m + 1
        self._max_cache[val] = ub
        return ub

    def _max_z3_optimize(self, val: BV):
        if USE_OPT_SOLVER:
            self._solver.push()
            h = self._solver.maximize(val.z3obj)
            assert self._solver.check().r == 1
            res = self._solver.upper(h).as_long()
            self._solver.pop()
        else:
            opt = z3.Optimize()
            for c in self.assertions:
                opt.add(c.z3obj)
            h = opt.maximize(val.z3obj)
            assert opt.check().r == 1
            res = opt.upper(h).as_long()
        return res

    def max(self, val: BV):
        if not symbolic(val):
            return val.value
        if val in self._max_cache:
            return self._max_cache[val]

        # res = self._max_binary_search(val)
        res = self._max_z3_optimize(val)
        val.interval.high = res

        self._max_cache[val] = res
        return res

    def _min_binary_search(self, val: BV):
        lb = 0
        ub = 2 ** val.size - 1
        while lb <= ub:
            m = (lb + ub) // 2
            if not self.satisfiable(extra_constraints=[val.ULE(m)]):
                lb = m + 1
            else:
                ub = m - 1
        return lb

    def _min_z3_optimize(self, val: BV):
        if USE_OPT_SOLVER:
            self._solver.push()
            h = self._solver.minimize(val.z3obj)
            assert self._solver.check().r == 1
            res = self._solver.lower(h).as_long()
            self._solver.pop()
        else:
            opt = z3.Optimize()
            for c in self.assertions:
                opt.add(c.z3obj)
            h = opt.minimize(val.z3obj)
            assert opt.check().r == 1
            res = opt.lower(h).as_long()
        return res

    def min(self, val: BV):
        if not symbolic(val):
            return val.value
        if val in self._min_cache:
            return self._min_cache[val]

        # res = self._min_binary_search(val)
        res = self._min_z3_optimize(val)
        val.interval.low = res

        self._min_cache[val] = res
        return res

    def model(self, extra_constraints: list = None):
        if extra_constraints:
            self._solver.push()
            self._add_tmp_constraints(*extra_constraints)

        assert self.satisfiable()
        res = self._solver.model()
        if extra_constraints:
            self._solver.pop()
        return res

    def _copy_cache(self, new, max_num_elem=3):
        i = 0
        for key in reversed(self._min_cache.keys()):
            if i > max_num_elem:
                break
            new._min_cache[key] = self._min_cache[key]
            i += 1
        i = 0
        for key in reversed(self._max_cache.keys()):
            if i > max_num_elem:
                break
            new._max_cache[key] = self._max_cache[key]
            i += 1
        i = 0
        for key in reversed(self._eval_cache.keys()):
            if i > max_num_elem:
                break
            new._eval_cache[key] = self._eval_cache[key]
            i += 1
        i = 0
        for key in reversed(self._symb_check_cache.keys()):
            if i > max_num_elem:
                break
            new._symb_check_cache[key] = self._symb_check_cache[key]
            i += 1

    def copy(self, state, fast_copy=False):
        fast_copy = True  # deepcopy seems broken

        res = Solver(state)
        if not fast_copy:
            # print("copying the solver slow")
            res._solver = self._solver.__deepcopy__()
            # print("copying done")
        else:
            for a in self._solver.assertions():
                res._solver.add(a)

        res.assertions = self.assertions[:]
        self._copy_cache(res, 3)
        return res

    def compute_solvers_difference(self, other):  # can be quite slow
        assert isinstance(other, Solver)

        i = 0
        for c1, c2 in zip(self.assertions, other.assertions):
            if not c1.eq(c2):
                break
            i += 1

        const1 = None
        for c in self.assertions[i:]:  # additional constraints self
            const1 = c if const1 is None else And(const1, c)

        const2 = None
        for c in other.assertions[i:]:  # additional constraints other
            const2 = c if const2 is None else And(const2, c)

        # common, consts only self, consts only other
        return self.assertions[:i], const1, const2

    def merge(self, other):
        assert isinstance(other, Solver)
        common, only_self, only_other = self.compute_solvers_difference(other)

        self._invalidate_cache()

        new_z3_solver = z3.Solver()
        self.assertions = []
        for const in common:
            new_z3_solver.add(const.z3obj)  # common constraints
            self.assertions.append(const)

        if only_self is not None and only_other is not None:
            cond = Or(only_self, only_other)
            cond = cond.simplify()
            if not cond.z3obj.eq(z3.BoolVal(True)):
                new_z3_solver.add(cond.z3obj)
                self.assertions.append(cond)
        else:
            raise Exception("Can this happen?")

        self._solver = new_z3_solver
