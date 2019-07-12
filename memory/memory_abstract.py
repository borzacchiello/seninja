import z3

class MemoryAbstract(object):
    def mmap(self, address: int, size: int, init):
        raise NotImplementedError
    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness):
        raise NotImplementedError
    def load(self, address: z3.BitVecRef, size: int, endness):
        raise NotImplementedError
    def get_unmapped(self, size, from_end):
        raise NotImplementedError
    def copy(self, state):
        raise NotImplementedError
