import z3

from enum import Enum
from copy import deepcopy
from .bitvector import BV, BVV, BVExpr
from .bool_expr import Bool, BoolV

class BVArrayState(Enum):
    # Never registered a symbolic memory access (either Load or Store)
    CONCRETE_MODE      = 0
    # Registered only a symbolic Load. Allowed concrete Load
    SEMI_CONCRETE_MODE = 1
    # Registered a symbolic Store
    SYMBOLIC_MODE      = 2


class BVArray(object):
    """ Wrapper of z3's Array. Beware: this is not immutable, differently from z3 """

    def __init__(self, name: str, index_width: int, value_width: int):
        assert index_width > 0
        assert value_width > 0

        self.name = name
        self.index_width = index_width
        self.value_width = value_width
        self._conc_store = {}
        self._assertions = list()
        self._z3obj = None
        self._z3objConcCache = None
        self._mode = BVArrayState.CONCRETE_MODE

    def __str__(self):
        return "<BVArray [BV{ind} -> BV{val}] {name}>".format(
            name=self.name,
            ind=self.index_width,
            val=self.value_width
        )

    def __repr__(self):
        return self.__str__()

    def get_mode(self):
        return self._mode

    def simplify(self):
        if self._z3obj is None:
            return
        self._z3obj = z3.simplify(self._z3obj)

    @property
    def z3obj(self):
        if self._z3obj is not None:
            # symbolic mode
            return self._z3obj

        # concrete mode
        if self._z3objConcCache is not None:
            return self._z3objConcCache
        res = z3.Array(
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

    def _switch_to_symbolic(self, soft=False):
        if self._mode == BVArrayState.SEMI_CONCRETE_MODE and soft:
            return

        if self._mode == BVArrayState.SEMI_CONCRETE_MODE and not soft:
            self._mode       = BVArrayState.SYMBOLIC_MODE
            self._conc_store = None
            return

        if self._mode == BVArrayState.CONCRETE_MODE:
            assert self._z3obj is None
            self._z3obj = z3.Array(
                self.name,
                z3.BitVecSort(self.index_width),
                z3.BitVecSort(self.value_width)
            )
            # The solver needs to add those constraints! (even lazly)
            for index in self._conc_store:
                self._assertions.append(
                    z3.Select(self._z3obj, index) == self._conc_store[index].z3obj
                )

            if soft:
                self._mode = BVArrayState.SEMI_CONCRETE_MODE
            else:
                self._mode = BVArrayState.SYMBOLIC_MODE
                self._conc_store = None

    def get_assertions(self):
        return self._assertions

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
            self._mode == BVArrayState.CONCRETE_MODE
        ):
            # concrete mode
            self._conc_store[index.value] = value
        else:
            # symbolic mode
            self._switch_to_symbolic(soft=False)
            self._z3obj = z3.Store(
                self._z3obj,
                index.z3obj,
                value.z3obj
            )

    def ConditionalStore(self, index, value, cond):
        if isinstance(index, int):
            index = BVV(index, self.index_width)
        else:
            assert index.size == self.index_width
        if isinstance(value, int):
            value = BVV(value, self.value_width)
        else:
            assert value.size == self.value_width
        if isinstance(cond, bool):
            cond = BoolV(cond)

        if isinstance(cond, BoolV):
            if cond.value:
                self.Store(index, value)
            return

        if (
            self._mode == BVArrayState.CONCRETE_MODE and
            isinstance(index, BVV) and
            index.value in self._conc_store and
            self._conc_store[index.value].eq(value)
        ):
            # the condition is symbolic, but the value is already in memory
            # we can safetely skip the store
            return

        self._switch_to_symbolic(soft=False)
        self._z3obj = z3.If(
            cond.z3obj,
            z3.Store(
                self._z3obj,
                index.z3obj,
                value.z3obj
            ),
            self._z3obj
        )
        # this can be quite inefficient.
        # Let's try to simplfy the expression.
        self._z3obj = z3.simplify(self._z3obj)

    def Select(self, index: BV) -> BV:
        if isinstance(index, int):
            index = BVV(index, self.index_width)
        else:
            assert index.size == self.index_width

        if (
            isinstance(index, BVV) and
            self._mode in {BVArrayState.CONCRETE_MODE, BVArrayState.SEMI_CONCRETE_MODE} and
            index.value in self._conc_store
        ):
            # concrete mode
            return self._conc_store[index.value]

        if (
            isinstance(index, BVV) and
            self._mode in {BVArrayState.CONCRETE_MODE, BVArrayState.SEMI_CONCRETE_MODE} and
            index.value not in self._conc_store
        ):
            # uninitialized read
            arr = z3.Array(
                self.name,
                z3.BitVecSort(self.index_width),
                z3.BitVecSort(self.value_width)
            )
            return BVExpr(self.value_width, z3.Select(arr, index.z3obj))

        # symbolic mode
        self._switch_to_symbolic(soft=True)
        return BVExpr(self.value_width, z3.Select(self._z3obj, index.z3obj))

    def copy(self):
        new = BVArray(self.name, self.index_width, self.value_width)
        new._conc_store = deepcopy(self._conc_store)
        new._z3obj = self._z3obj

        return new

    def merge(self, other, merge_condition: Bool):
        assert self.name == other.name
        assert self.index_width == other.index_width
        assert self.value_width == other.value_width
        if isinstance(merge_condition, BoolV):
            if merge_condition.value:
                return other.copy()
            return self

        # FIXME: broken!! Handle assertions

        self._switch_to_symbolic()
        self._z3obj = z3.If(
            merge_condition.z3obj,
            other.z3obj,
            self._z3obj
        )
        # this can be quite inefficient.
        # Let's try to simplfy the expression.
        self._z3obj = z3.simplify(self._z3obj)
        return self
