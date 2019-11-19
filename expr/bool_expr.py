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
        return "<BoolExpr {obj}>".format(
            obj=str(self.z3obj)
        )
    
    def simplify(self):
        self.z3obj = z3.simplify(self.z3obj)

    def eq(self, other: Bool):
        return self.z3obj == other.z3obj

    def __eq__(self, other: Bool):
        return BoolExpr(self.z3obj == other.z3obj)

    def __neq__(self, other: Bool):
        return BoolExpr(self.z3obj != other.z3obj)
    
    def Not(self):
        return BoolExpr(z3.Not(self.z3obj))

    def Or(self, other: Bool):
        return BoolExpr(z3.Or(self.z3obj, other.z3obj))

    def And(self, other: Bool):
        return BoolExpr(z3.And(self.z3obj, other.z3obj))

    def Xor(self, other: Bool):
        return BoolExpr(z3.Xor(self.z3obj, other.z3obj))


class BoolS(BoolExpr):
    def __init__(self, name):
        self.name  = name
        self.z3obj = z3.Bool(name)

    def __str__(self):
        return "<BoolS {name}>".format(
            name=str(self.name)
        )

class BoolV(Bool):
    def __init__(self, value: bool):
        self.value = value

    @property
    def z3obj(self):
        return z3.BoolVal(self.value)
    
    def simplify(self):
        return

    def __str__(self):
        return "<BoolV {val}>".format(
            val=str(self.value)
        )
    
    def eq(self, other: Bool):
        return isinstance(other, BoolV) and other.value == self.value

    def __eq__(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value == other.value)
        return BoolExpr(self.z3obj == other.z3obj)

    def __neq__(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value != other.value)
        return BoolExpr(self.z3obj != other.z3obj)
    
    def Not(self):
        return BoolV(not self.value)
    
    def Or(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value or other.value)
        return BoolExpr(z3.Or(self.z3obj, other.z3obj))

    def And(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(self.value and other.value)
        return BoolExpr(z3.And(self.z3obj, other.z3obj))

    def Xor(self, other: Bool):
        if isinstance(other, BoolV):
            return BoolV(
                (self.value or other.value) and not (self.value and other.value)
            )
        return BoolExpr(z3.Xor(self.z3obj, other.z3obj))
