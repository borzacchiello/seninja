class Interval(object):
    def __init__(self, bits, low=None, high=None):
        assert bits > 0
        self.bits = bits
        self.max = (2 << (bits - 1)) - 1
        self.low = low if low is not None else 0
        self.high = high if high is not None else self.max

        self.low = self.low & self.max
        self.high = self.high & self.max

        assert self.high >= self.low
    
    def __str__(self):
        return "<Interval%d [%s -> %s]>" % (
            self.bits, hex(self.low), hex(self.high)
        )
    
    def __repr__(self):
        return self.__str__()

    @property
    def is_top(self):
        return self.low == 0 and self.high == self.max

    def __add__(self, other):
        assert other.bits == self.bits

        new_low = self.low + other.low
        new_high = self.high + other.high
        if new_high > self.max:
            new_high = self.max
            new_low = 0

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __sub__(self, other):
        assert other.bits == self.bits

        new_low = self.low - other.low
        new_high = self.high - other.high
        if new_low < 0:
            new_high = self.max
            new_low = 0

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __mul__(self, other):
        assert other.bits == self.bits

        new_low = self.low * other.low
        new_high = self.high * other.high
        if new_high > self.max:
            new_high = self.max
            new_low = 0

        return Interval(
            self.bits,
            new_low,
            new_high
        )
    
    def __truediv__(self, other):
        assert other.bits == self.bits
        return Interval(self.bits)

    def __mod__(self, other):
        assert other.bits == self.bits

        new_low = 0
        new_high = other.high

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __xor__(self, other):
        assert other.bits == self.bits

        new_low = 0
        new_high = max(self.high, other.high)

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __and__(self, other):
        assert other.bits == self.bits

        new_low = 0
        new_high = self.high & other.high

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __or__(self, other):
        assert other.bits == self.bits

        new_low = 0
        new_high = max(self.high, other.high)

        return Interval(
            self.bits,
            new_low,
            new_high
        )
    
    def __lshift__(self, other):
        # arithmetic/logical left shift
        assert other.bits == self.bits

        new_low = self.low << other.low
        new_high = self.high << other.high
        if new_high > self.max:
            new_high = self.max
            new_low = 0

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __rshift__(self, other):
        # arithmetic right shift
        assert other.bits == self.bits

        new_low = self.low >> other.low
        # check sign
        if self.high >> (self.bits-1) == 1:
            new_high = self.high
        else:
            new_high = self.high >> other.high

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def __invert__(self):
        return Interval(self.bits)
    
    def __neg__(self):
        return Interval(self.bits)

    def UDiv(self, other):
        assert other.bits == self.bits

        new_low = self.low // other.low
        new_high = self.high // other.high

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def SDiv(self, other):
        return self.__truediv__(other)

    def URem(self, other):
        assert other.bits == self.bits
        return Interval(self.bits)

    def SRem(self, other):
        assert other.bits == self.bits
        return Interval(self.bits)
    
    def LShL(self, other):
        return self.__lshift__(other)

    def AShL(self, other):
        # arithmetic and logical left shift are identical
        return self.__lshift__(other)

    def LShR(self, other):
        assert other.bits == self.bits

        new_low = self.low >> other.low
        new_high = self.high >> other.high

        return Interval(
            self.bits,
            new_low,
            new_high
        )

    def AShR(self, other):
        return self.__rshift__(other)

    def RotateLeft(self, other):
        assert self.bits == other.bits
        return Interval(self.bits)

    def RotateRight(self, other):
        assert self.bits == other.bits
        return Interval(self.bits)

    def Concat(self, other):
        new_low = (self.low << other.bits) + other.low
        new_high = (self.high << other.bits) + other.high

        return Interval(
            self.bits + other.bits,
            new_low,
            new_high
        )

    def Extract(self, high: int, low: int):
        new_low = min(self.low >> low, (2 << (high - low)) - 1)
        new_high = min(self.high >> low, (2 << (high - low)) - 1)

        return Interval(
            high - low + 1,
            new_low,
            new_high
        )

    def SignExt(self, n: int):
        assert n >= 0
        new_low = self.low
        if self.high >> (self.bits-1) == 1:
            new_high = (2 << (self.bits + n - 1)) - 1
        else:
            new_high = self.high

        return Interval(
            self.bits + n,
            new_low,
            new_high
        )

    def ZeroExt(self, n: int):
        assert n >= 0
        return Interval(
            self.bits + n,
            self.low,
            self.high
        )
