import z3

class MemoryAbstract(object):
    def mmap(self, address: int, size: int, init):
        raise NotImplementedError
    def is_mapped(self, address: int):
        raise NotImplementedError
    def store(self, address: z3.BitVecRef, value: z3.BitVecRef, endness):
        raise NotImplementedError
    def load(self, address: z3.BitVecRef, size: int, endness):
        raise NotImplementedError
    def get_unmapped(self, size: int, start_from: int, from_end: int):
        raise NotImplementedError
    def allocate(self, size: int, init):
        raise NotImplementedError
    def copy(self, state):
        raise NotImplementedError
    def merge(self, other, merge_condition):
        raise NotImplementedError
    def register_read_hook(self, function):
        raise NotImplementedError
    def register_store_hook(self, function):
        raise NotImplementedError
