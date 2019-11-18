import z3

class Bool(object):
    def __init__(self):
        # do not instantiate this class
        raise NotImplementedError

    def __repr__(self):
        return self.__str__()

class BoolExpr(Bool):
    def __init__(self, z3obj):
        self.z3obj = z3obj

    def __str__(self):
        return "<BoolExpr {obj}".format(
            obj=str(self.z3obj)
        )

    def __eq__(self, other: Bool):
        return BoolExpr(self.z3obj == other.z3obj)

    def __neq__(self, other: Bool):
        return BoolExpr(self.z3obj != other.z3obj)

class BoolS(BoolExpr):
    def __init__(self, name):
        self.name  = name
        self.z3obj = z3.Bool(name)

    def __str__(self):
        return "<BoolS {name}".format(
            name=str(self.name)
        )

class BoolV(Bool):
    def __init__(self, value: bool):
        self.value = value

    @property
    def z3obj(self):
        return z3.BoolVal(self.value)

    def __str__(self):
        return "<BoolV {val}".format(
            val=str(self.value)
        )

    def __eq__(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value == other.value)
        return BoolExpr(self.z3obj == other.z3obj)

    def __neq__(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value != other.value)
        return BoolExpr(self.z3obj != other.z3obj)
