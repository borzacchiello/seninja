from copy import deepcopy
import z3

class Solver(object):
    def __init__(self, state):
        self.state   = state
        self._solver = z3.Solver()
    
    def add_constraints(self, *constraints):
        for c in constraints:
            c = z3.simplify(c)
            if not z3.BoolVal(True).eq(c):
                self._solver.add(z3.simplify(c))
    
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
        res = model.evaluate(var, model_completion=True).as_long()
        
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        return res

    def evaluate(self, var, extra_constraints: list=[]) -> z3.BitVecRef:
        assert self.satisfiable(extra_constraints)
        if extra_constraints:
            self._solver.push()
            self.add_constraints(*extra_constraints)

        model = self._solver.model()
        res = model.evaluate(var, model_completion=False)
        
        if extra_constraints:
            self._solver.pop()
            extra_constraints = []
        return res
    
    def evaluate_upto(self, var, n, extra_constraints: list=[]) -> list:
        assert self.satisfiable(extra_constraints)
        self._solver.push()
        if extra_constraints:
            self.add_constraints(*extra_constraints)
        
        res = list()
        while n > 0 and self.satisfiable():
            model = self._solver.model()
            r = model.evaluate(var, model_completion=True).as_long()
            res.append(r)
            self.add_constraints(var != r)
            n -= 1
        
        self._solver.pop()
        extra_constraints = []
        return res
    
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

    def copy(self):
        res = Solver(self.state)
        res._solver = deepcopy(self._solver)
        return res
