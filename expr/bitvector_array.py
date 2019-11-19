from copy import deepcopy
from expr.bitvector import BV, BVV, BVExpr
import z3

class BVArray(object):
    """ Wrapper of z3's Array. Beware: this is not immutable, differently from z3 """
    def __init__(self, name: str, index_width: int, value_width: int):
        assert index_width > 0
        assert value_width > 0

        self.name = name
        self.index_width = index_width
        self.value_width = value_width
        self._conc_store = {}
        self._z3obj = None
        self._z3objConcCache = None
    
    def __str__(self):
        return "<BVArray [BV{ind} -> BV{val}] {name}>".format(
            name = self.name,
            ind  = self.index_width,
            val  = self.value_width
        )
    
    def __repr__(self):
        return self.__str__()
    
    @property
    def z3obj(self):
        if self._z3obj is not None:
            # symbolic mode
            return self._z3obj
        
        # concrete mode
        if self._z3objConcCache is not None:
            return self._z3objConcCache
        res = z3.Array (
            self.name, 
            z3.BitVecSort(self.index_width), 
            z3.BitVecSort(self.value_width)
        )
        for index in self._conc_store:
            res = z3.Store(
                res,
                z3.BitVecVal(index, self.index_width),
                self._conc_store[index].z3obj
            )
        self._z3objConcCache = res
        return res
    
    def _switch_to_symbolic(self):
        if self._conc_store is not None:
            assert self._z3obj is None
            self._z3obj = z3.Array (
                self.name, 
                z3.BitVecSort(self.index_width), 
                z3.BitVecSort(self.value_width)
            )
            for index in self._conc_store:
                self._z3obj = z3.Store (
                    self._z3obj,
                    z3.BitVecVal(index, self.index_width),
                    self._conc_store[index].z3obj
                )
            
            self._conc_store = None
    
    def Store(self, index, value):
        if isinstance(index, int):
            index = BVV(index, self.index_width)
        else:
            assert index.size == self.index_width
        if isinstance(value, int):
            value = BVV(value, self.value_width)
        else:
            assert value.size == self.value_width
        
        # invalidate cache
        self._z3objConcCache = None

        if (
            isinstance(index, BVV) and 
            self._conc_store is not None
        ):
            # concrete mode
            self._conc_store[index.value] = value
        else:
            # symbolic mode
            self._switch_to_symbolic()
            self._z3obj = z3.Store(
                self._z3obj,
                index.z3obj,
                value.z3obj
            )
    
    def Select(self, index: BV) -> BV:
        if isinstance(index, int):
            index = BVV(index, self.index_width)
        else:
            assert index.size == self.index_width

        if (
            isinstance(index, BVV) and 
            self._conc_store is not None and
            index.value in self._conc_store
        ):
            # concrete mode
            return self._conc_store[index.value]
        
        # symbolic mode
        # no need to switch to symbolic mode! (is this right?)
        return BVExpr(self.value_width,
            z3.Select(
                self.z3obj,
                index.z3obj
            )
        )

    def copy(self):
        new = BVArray(self.name, self.index_width, self.value_width)
        new._conc_store = deepcopy(self._conc_store)
        new._z3obj = self._z3obj

        return new