from ..expr import BV, BVArray, Bool, ITE

class MemoryObj(object):
    def __init__(self, name, bits=64, bvarray=None):
        self.bvarray = BVArray (
            "MEMOBJ_" + name, bits, 8
        ) if bvarray is None else bvarray

        self.name = name
        self.bits = bits
    
    def __str__(self):
        return "<MemoryObj{bits} {name}>".format(
            bits = self.bits,
            name = self.name
        )
    
    def __repr__(self):
        return self.__str__()
    
    def load(self, index: BV):
        return self.bvarray.Select(index)
    
    def store(self, index: BV, value: BV, condition: Bool=None):
        if condition is None:
            self.bvarray.Store(index, value)
        else:
            # this can be inefficient
            self.bvarray.ConditionalStore(index, value, condition)

    def copy(self):
        return MemoryObj(self.name, self.bits, self.bvarray.copy())
    
    def merge(self, other, merge_condition: Bool):
        self.bvarray = self.bvarray.merge(other.bvarray, merge_condition)
