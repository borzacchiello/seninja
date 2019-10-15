from copy import deepcopy
import utility.z3_wrap_util as z3w
import z3

class Solver(object):
    def __init__(self, state):
        self.state   = state
        self._solver = z3.Solver()
        self._min_cache  = {}
        self._max_cache  = {}
        self._eval_cache = {}
        self._symb_check_cache = {}
    
    def _invalidate_cache(self):
        self._min_cache = {}
        self._max_cache = {}
        self._eval_cache = {}
        self._symb_check_cache = {}

    def add_constraints(self, *constraints):
        self._invalidate_cache()
        for c in constraints:
            c = z3.simplify(c)
            if not z3.BoolVal(True).eq(c):
                self._solver.add(c)
    
    def satisfiable(self, extra_constraints: list=[]):
        if extra_constraints:
            self._solver.push()
            self.add_constraints(*extra_constraints)
        
        res = self._solver.check().r == 1
        
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        return res
    
    def evaluate_long(self, var, extra_constraints: list=[]) -> int:
        assert self.satisfiable(extra_constraints)
        if extra_constraints:
            self._solver.push()
            self.add_constraints(*extra_constraints)

        model = self._solver.model()
        res = model.evaluate(var, model_completion=True)
        res = res.as_long()
        
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        return res

    def evaluate(self, var, extra_constraints: list=[]) -> z3.BitVecRef:
        assert self.satisfiable(extra_constraints)
        if extra_constraints:
            self._solver.push()
            self.add_constraints(*extra_constraints)
        elif var in self._eval_cache:
            return self._eval_cache[var]

        model = self._solver.model()
        res = model.evaluate(var, model_completion=False)
        
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        else:
            self._eval_cache[var] = res
        return res
    
    def evaluate_upto(self, var, n, extra_constraints: list=[]) -> list:
        assert self.satisfiable(extra_constraints)
        self._solver.push()
        if extra_constraints:
            self.add_constraints(*extra_constraints)
        
        res = list()
        while n > 0 and self.satisfiable():
            model = self._solver.model()
            r = model.evaluate(var, model_completion=True)
            r = r.as_long()
            res.append(r)
            self.add_constraints(var != r)
            n -= 1
        
        self._solver.pop()
        extra_constraints = []
        return res
    
    def symbolic(self, val: z3.BitVecRef):
        if val in self._symb_check_cache:
            return self._symb_check_cache[val]
        
        res = len(self.evaluate_upto(val, 2)) != 1
        self._symb_check_cache[val] = res
        return res
    
    def max(self, val: z3.BitVecRef):
        if not z3w.symbolic(val):
            return z3.simplify(val).as_long()
        if val in self._max_cache:
            return self._max_cache[val]
        lb = 0
        ub = 2 ** val.size() - 1
        while lb <= ub:
            m = (lb + ub) // 2
            if not self.satisfiable(extra_constraints=[z3.UGE(val, m)]):
                ub = m - 1
            else:
                lb = m + 1
        self._max_cache[val] = ub
        return ub
    
    def min(self, val: z3.BitVecRef):
        if not z3w.symbolic(val):
            return z3.simplify(val).as_long()
        if val in self._min_cache:
            return self._min_cache[val]
        lb = 0
        ub = 2 ** val.size() - 1
        while lb <= ub:
            m = (lb + ub) // 2
            if not self.satisfiable(extra_constraints=[z3.ULE(val,  m)]):
                lb = m + 1
            else:
                ub = m - 1
        self._min_cache[val] = lb
        return lb
    
    def model(self, extra_constraints: list=[]):
        assert self.satisfiable(extra_constraints)
        if extra_constraints:
            self._solver.push()
            self.add_constraints(*extra_constraints)
        
        res = self._solver.model()
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        return res

    def copy(self, state, fast_copy=False):
        res = Solver(state)
        if not fast_copy:
            # print("copying the solver slow")
            res._solver = deepcopy(self._solver)
            # print("copying done")
        else:
            for a in self._solver.assertions():
                res._solver.add(a)
        return res
    
    def compute_solvers_difference(self, other):  # can be quite slow
        assert isinstance(other, Solver)

        i = 0
        for c1, c2 in zip(self._solver.assertions(), other._solver.assertions()):
            if not c1.eq(c2):
                break
            i += 1

        const1 = None
        for c in self._solver.assertions()[i:]:  # additional constraints self
            const1 = c if const1 is None else z3.And(const1, c)
        
        const2 = None
        for c in other._solver.assertions()[i:]: # additional constraints other
            const2 = c if const2 is None else z3.And(const2, c)
        
        # common, consts only self, consts only other
        return self._solver.assertions()[:i], const1, const2

    def merge(self, other):
        assert isinstance(other, Solver)
        common, only_self, only_other = self.compute_solvers_difference(other)
        
        new_z3_solver = z3.Solver()
        new_z3_solver.add(*common)  # common constraints
        
        if only_self is not None and only_other is not None:
            cond = z3.simplify(z3.Or(only_self, only_other))
            if not cond.eq(z3.BoolVal(True)):
                new_z3_solver.add(cond)
        else:
            raise Exception("Can this happen?")
        
        self._solver = new_z3_solver
