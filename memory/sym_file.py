from ..expr import BV, BVV, BVS
from .sym_flat_memory_not_paged import MemoryConcreteFlatNotPaged


class SymFile(object):
    def __init__(self, filename, symfile=None):
        self.filename = filename
        if symfile is None:
            self.data = MemoryConcreteFlatNotPaged(filename)
            self.seek_idx = 0
            self.file_size = 0
        else:
            self.data = symfile.data.copy()
            self.seek_idx = symfile.seek_idx
            self.file_size = symfile.file_size

    def __str__(self):
        return "<SymFile %s>" % self.filename

    def __repr__(self):
        return self.__str__()

    def seek(self, idx: int):
        self.seek_idx = idx

    def read(self, size: int) -> list:
        res = []
        for i in range(self.seek_idx, self.seek_idx + size):
            res.append(self.data.load(BVV(i, self.data.bits), 1))

        self.seek_idx += size
        self.file_size = max(self.file_size, self.seek_idx)
        return res

    def write(self, data: list):
        for i, el in enumerate(data):
            assert isinstance(el, BV) and el.size == 8
            self.data.store(
                BVV(self.seek_idx + i, 64),
                el
            )

        self.seek_idx += len(data)
        self.file_size = max(self.file_size, self.seek_idx)

    def merge(self, other, merge_condition):
        pass  # not implemented

    def copy(self, state=None):
        return SymFile(self.filename, self)
