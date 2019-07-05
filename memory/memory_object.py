import z3

class MemoryObj(object):
    def __init__(self, name, bits=64):
        index_sort  = z3.BitVecSort(bits)
        value_sort  = z3.BitVecSort(8)
        self._z3obj = z3.Array("MEMOBJ_" + name, index_sort, value_sort)

        self.name = name
        self.bits = bits
    
    def simplify(self):
        self._z3obj = z3.simplify(self._z3obj)
    
    def load(self, index: z3.BitVecRef):
        return z3.simplify(z3.Select(self._z3obj, index))
    
    def store(self, index: z3.BitVecRef, value: z3.BitVecRef, condition: z3.BoolRef=None):
        index = z3.simplify(index)
        value = z3.simplify(value)
        if condition is None:
            self._z3obj = z3.Store(self._z3obj, index, value)
        else:
            self._z3obj = z3.simplify(
                z3.If(condition, 
                    z3.simplify(z3.Store(self._z3obj, index, value)), 
                    self._z3obj))

    def copy(self):
        res = MemoryObj(self.name, self.bits)
        res._z3obj = self._z3obj
        return res
