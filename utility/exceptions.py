# ERRORS
class SENinjaError(Exception):
    def is_fatal(self):
        raise NotImplementedError # override

class DivByZero(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "Division by zero occurred at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False

class UnmappedRead(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "Unmapped read at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False

class UnmappedWrite(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "Unmapped write at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False

class NoDestination(SENinjaError):
    def __init__(self):
        self.message = "No destination"
        super().__init__(self.message)

    def is_fatal(self):
        return False

class UnconstrainedIp(SENinjaError):
    def __init__(self):
        self.message = "Unconstrained ip"
        super().__init__(self.message)

    def is_fatal(self):
        return False

class UnsatState(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "UNSAT state at 0x%x"
        super().__init__(self.message)

    def is_fatal(self):
        return True

class UnimplementedInstruction(SENinjaError):
    def __init__(self, instr_name):
        self.instr_name = instr_name
        self.message = "%s instruction is unimplemented" % instr_name
        super().__init__(self.message)

    def is_fatal(self):
        return True

# *****

class SENinjaExeption(Exception):
    pass

class ExitException(SENinjaExeption):
    pass
