import z3

from .bool_expr import BoolExpr, BoolV
from .interval import Interval


class BV(object):
    def __init__(self):
        # do not instantiate this class
        raise NotImplementedError

    def __repr__(self):
        return self.__str__()

    def __neg__(self):
        raise NotImplementedError

    def __add__(self, other):
        raise NotImplementedError

    def __sub__(self, other):
        raise NotImplementedError

    def __mul__(self, other):
        raise NotImplementedError

    def __radd__(self, other):
        return self.__add__(other)

    def __rsub__(self, other):
        return self.__neg__().__add__(other)

    def __rmul__(self, other):
        return self.__mul__(other)


class BVExpr(BV):
    def __init__(self, size: int, z3obj, interval=None):
        self.z3obj = z3obj
        self.size = size
        self.interval = interval if interval is not None else Interval(
            self.size)

    def __str__(self):
        return "<BVExpr{size} {obj}>".format(
            size=self.size, obj=str(self.z3obj)
        )

    def simplify(self):
        simplified = z3.simplify(self.z3obj)
        if simplified.decl().kind() == z3.Z3_OP_BNUM:
            return BVV(simplified.as_long(), self.size)
        if simplified.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            return BVS(simplified.sexpr(), self.size)
        if not simplified.eq(self.z3obj):
            return BVExpr(self.size, simplified, self.interval)
        return self

    def eq(self, other):
        if not isinstance(other, BV):
            return False
        return self.z3obj.eq(other.z3obj)

    def __hash__(self):
        return self.z3obj.__hash__()

    def __add__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj + other.z3obj, self.interval + other.interval)

    def __sub__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj - other.z3obj, self.interval - other.interval)

    def __mul__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj * other.z3obj, self.interval * other.interval)

    def __truediv__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj / other.z3obj, self.interval / other.interval)

    def __mod__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj % other.z3obj, self.interval % other.interval)

    def __xor__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj ^ other.z3obj, self.interval ^ other.interval)

    def __and__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj & other.z3obj, self.interval & other.interval)

    def __or__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj | other.z3obj, self.interval | other.interval)

    def __lshift__(self, other):
        # arithmetic/logical left shift
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, self.z3obj << other.z3obj, self.interval << other.interval)

    def __rshift__(self, other):
        # arithmetic right shift
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        new_interval = self.interval.LShR(other.interval)
        if new_interval.low == new_interval.high:
            # concrete path
            return BVV(new_interval.low, self.size)
        return BVExpr(self.size, self.z3obj >> other.z3obj, new_interval)

    def __eq__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj == other.z3obj)

    def __ne__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj != other.z3obj)

    def __lt__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj < other.z3obj)

    def __le__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj <= other.z3obj)

    def __gt__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj > other.z3obj)

    def __ge__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(self.z3obj >= other.z3obj)

    def __invert__(self):
        return BVExpr(self.size, self.z3obj.__invert__(), self.interval.__invert__())

    def __neg__(self):
        return BVExpr(self.size, self.z3obj.__neg__(), self.interval.__neg__())

    def UDiv(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, z3.UDiv(self.z3obj, other.z3obj), self.interval.UDiv(other.interval))

    def SDiv(self, other):
        return self.__truediv__(other)

    def URem(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, z3.URem(self.z3obj, other.z3obj), self.interval.URem(other.interval))

    def SRem(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, z3.SRem(self.z3obj, other.z3obj), self.interval.SRem(other.interval))

    def LShL(self, other):
        return self.__lshift__(other)

    def AShL(self, other):
        # arithmetic and logical left shift are identical
        return self.__lshift__(other)

    def LShR(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        new_interval = self.interval.LShR(other.interval)
        if new_interval.low == new_interval.high:
            # concrete path
            return BVV(new_interval.low, self.size)
        return BVExpr(self.size, z3.LShR(self.z3obj, other.z3obj), new_interval)

    def AShR(self, other):
        return self.__rshift__(other)

    def ULT(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(z3.ULT(self.z3obj, other.z3obj))

    def ULE(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(z3.ULE(self.z3obj, other.z3obj))

    def UGT(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(z3.UGT(self.z3obj, other.z3obj))

    def UGE(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BoolExpr(z3.UGE(self.z3obj, other.z3obj))

    def SLT(self, other):
        return self.__lt__(other)

    def SLE(self, other):
        return self.__le__(other)

    def SGT(self, other):
        return self.__gt__(other)

    def SGE(self, other):
        return self.__ge__(other)

    def RotateLeft(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, z3.RotateLeft(self.z3obj, other.z3obj), self.interval.RotateLeft(other.interval))

    def RotateRight(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        return BVExpr(self.size, z3.RotateRight(self.z3obj, other.z3obj), self.interval.RotateRight(other.interval))

    def Concat(self, other: BV):
        return BVExpr(self.size + other.size, z3.Concat(self.z3obj, other.z3obj), self.interval.Concat(other.interval))

    def Extract(self, high: int, low: int):
        assert high >= low
        new_interval = self.interval.Extract(high, low)
        if new_interval.high == new_interval.low:
            # extract is concrete
            return BVV(new_interval.high, high-low+1)
        return BVExpr(high-low+1, z3.Extract(high, low, self.z3obj), new_interval)

    def SignExt(self, n: int):
        assert n >= 0
        return BVExpr(self.size + n, z3.SignExt(n, self.z3obj), self.interval.SignExt(n))

    def ZeroExt(self, n: int):
        assert n >= 0
        return BVExpr(self.size + n, z3.ZeroExt(n, self.z3obj), self.interval.ZeroExt(n))


class BVS(BVExpr):
    def __init__(self, name: str, size: int):
        self.name = name
        self.size = size
        self.z3obj = z3.BitVec(name, size)

    def __str__(self):
        return "<BVS{size} {obj}>".format(
            size=self.size, obj=str(self.z3obj)
        )

    def simplify(self):
        return self

    @property
    def interval(self):
        return Interval(self.size)


class BVV(BV):
    def __init__(self, value: int, size: int):
        self.size = size
        self._mask = (2 << (size-1)) - 1
        self.value = value & self._mask
        self._signMask = 2 << (size-1-1) if size > 1 else 0

    def as_bytes(self):
        assert self.size % 8 == 0
        res = b""
        for i in range(0, self.size, 8):
            bv = self.Extract(i+8-1, i)
            res = bytes([bv.value]) + res
        return res

    def simplify(self):
        return self

    @property
    def z3obj(self):
        return z3.BitVecVal(self.value, self.size)

    @property
    def interval(self):
        return Interval(self.size, self.value, self.value)

    def __str__(self):
        return "<BVV{size} 0x{obj:0{width}x}>".format(
            size=self.size, obj=self.value,
            width=(self.size+3) // 4
        )

    def eq(self, other):
        if not isinstance(other, BV):
            return False
        if isinstance(other, BVV):
            return self.value == other.value and \
                self.size == other.size
        return self.z3obj.eq(other.z3obj)

    def __hash__(self):
        return hash((self.value, self.size))

    def __add__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value + other.value) & self._mask, self.size)
        return BVExpr(self.size, self.value + other.z3obj, self.interval + other.interval)

    def __sub__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value - other.value) & self._mask, self.size)
        return BVExpr(self.size, self.value - other.z3obj, self.interval - other.interval)

    def __mul__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value * other.value) & self._mask, self.size)
        return BVExpr(self.size, self.value * other.z3obj, self.interval * other.interval)

    def __truediv__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            # python round up -x.y to -(x+1). Z3 round up to -x
            # We want to be consistent with Z3
            sign = 1 if signed_left * signed_right > 0 else -1
            value = abs(signed_left) // abs(signed_right)
            return BVV((sign * value) & self._mask, self.size)
        return BVExpr(self.size, self.z3obj / other.z3obj, self.interval / other.interval)

    def __mod__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            return BVV((signed_left % signed_right) & self._mask, self.size)
        return BVExpr(self.size, self.z3obj % other.z3obj, self.interval % other.interval)

    def __xor__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value ^ other.value) & self._mask, self.size)
        return BVExpr(self.size, self.value ^ other.z3obj, self.interval ^ other.interval)

    def __and__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value & other.value) & self._mask, self.size)
        return BVExpr(self.size, self.z3obj & other.z3obj, self.interval & other.interval)

    def __or__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value | other.value) & self._mask, self.size)
        return BVExpr(self.size, self.z3obj | other.z3obj, self.interval | other.interval)

    def __lshift__(self, other):
        # arithmetic/logical left shift
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value << other.value) & self._mask, self.size)
        return BVExpr(self.size, self.z3obj << other.z3obj, self.interval << other.interval)

    def __rshift__(self, other):
        # arithmetic right shift
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            tmp = self._signMask >> other.value
            new = ((self.value >> other.value) ^ tmp) - tmp
            return BVV(new & self._mask, self.size)
        return BVExpr(self.size, self.z3obj >> other.z3obj, self.interval >> other.interval)

    def __eq__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value == other.value)
        return BoolExpr(self.z3obj == other.z3obj)

    def __ne__(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value != other.value)
        return BoolExpr(self.z3obj != other.z3obj)

    def __lt__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            return BoolV(signed_left < signed_right)
        return BoolExpr(self.z3obj < other.z3obj)

    def __le__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            return BoolV(signed_left <= signed_right)
        return BoolExpr(self.z3obj <= other.z3obj)

    def __gt__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            return BoolV(signed_left > signed_right)
        return BoolExpr(self.z3obj > other.z3obj)

    def __ge__(self, other):
        # signed
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            return BoolV(signed_left >= signed_right)
        return BoolExpr(self.z3obj >= other.z3obj)

    def __invert__(self):
        return BVV(~self.value, self.size)

    def __neg__(self):
        return BVV(-self.value, self.size)

    def UDiv(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value // other.value) & self._mask, self.size)
        return BVExpr(self.size, z3.UDiv(self.z3obj, other.z3obj), self.interval.UDiv(other.interval))

    def SDiv(self, other):
        return self.__truediv__(other)

    def URem(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value % other.value) & self._mask, self.size)
        return BVExpr(self.size, z3.URem(self.z3obj, other.z3obj), self.interval.URem(other.interval))

    def SRem(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            signed_left = (self.value - 2**self.size) \
                if self.value & self._signMask else self.value
            signed_right = (other.value - 2**other.size) \
                if other.value & other._signMask else other.value
            # sign div
            sign = 1 if signed_left * signed_right > 0 else -1
            div_abs = abs(signed_left) // abs(signed_right)
            div = sign * div_abs
            # sign rem
            rem = signed_left - (signed_right * div)
            return BVV(rem, self.size)
        return BVExpr(self.size, z3.SRem(self.z3obj, other.z3obj), self.interval.SRem(other.interval))

    def LShL(self, other):
        return self.__lshift__(other)

    def AShL(self, other):
        # arithmetic and logical left shift are identical
        return self.__lshift__(other)

    def LShR(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BVV((self.value >> other.value) & self._mask, self.size)
        return BVExpr(self.size, z3.LShR(self.z3obj, other.z3obj), self.interval.LShR(other.interval))

    def AShR(self, other):
        return self.__rshift__(other)

    def ULT(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value < other.value)
        return BoolExpr(z3.ULT(self.z3obj, other.z3obj))

    def ULE(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value <= other.value)
        return BoolExpr(z3.ULE(self.z3obj, other.z3obj))

    def UGT(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value > other.value)
        return BoolExpr(z3.UGT(self.z3obj, other.z3obj))

    def UGE(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            return BoolV(self.value >= other.value)
        return BoolExpr(z3.UGE(self.z3obj, other.z3obj))

    def SLT(self, other):
        return self.__lt__(other)

    def SLE(self, other):
        return self.__le__(other)

    def SGT(self, other):
        return self.__gt__(other)

    def SGE(self, other):
        return self.__ge__(other)

    def RotateLeft(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            other_norm = other.value % self.size
            new = (((self.value << other_norm) & self._mask) |
                   ((self.value >> ((self.size - other_norm) & self._mask)) & self._mask))
            return BVV(new & self._mask, self.size)
        return BVExpr(self.size, z3.RotateLeft(self.z3obj, other.z3obj), self.interval.RotateLeft(other.interval))

    def RotateRight(self, other):
        if isinstance(other, int):
            other = BVV(other, self.size)
        else:
            assert isinstance(other, BV)
            assert self.size == other.size
        if isinstance(other, BVV):
            other_norm = other.value % self.size
            new = (((self.value >> other_norm) & self._mask) |
                   ((self.value << ((self.size - other_norm) & self._mask)) & self._mask))
            return BVV(new & self._mask, self.size)
        return BVExpr(self.size, z3.RotateRight(self.z3obj, other.z3obj), self.interval.RotateRight(other.interval))

    def Concat(self, other: BV):
        if isinstance(other, BVV):
            new_value = (self.value << other.size) + other.value
            new_size = self.size + other.size
            new_mask = 2**new_size-1
            return BVV(new_value & new_mask, new_size)
        return BVExpr(self.size + other.size, z3.Concat(self.z3obj, other.z3obj), self.interval.Concat(other.interval))

    def Extract(self, high: int, low: int):
        assert high >= low
        new_size = high-low+1
        new_value = (self.value >> low) & ((2 << (new_size-1))-1)
        return BVV(new_value, new_size)

    def SignExt(self, n: int):
        assert n >= 0
        if self._signMask & self.value:
            new = (((2 << (n-1))-1) << self.size) + self.value
        else:
            new = self.value
        mask = (2 << (self.size+n-1))-1
        return BVV(new & mask, self.size + n)

    def ZeroExt(self, n: int):
        assert n >= 0
        return BVV(self.value, self.size + n)
