# ERRORS
class SENinjaError(Exception):
    def __init__(self, msg):
        self.message = msg
        super().__init__(msg)

    def is_fatal(self):
        raise NotImplementedError  # override


class DivByZero(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "division by zero occurred at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False


class UnmappedRead(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "unmapped read at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False


class UnmappedWrite(SENinjaError):
    def __init__(self, pc):
        self.pc = pc
        self.message = "unmapped write at 0x%x" % pc
        super().__init__(self.message)

    def is_fatal(self):
        return False


class NoDestination(SENinjaError):
    def __init__(self):
        self.message = "no destination"
        super().__init__(self.message)

    def is_fatal(self):
        return False


class UnconstrainedIp(SENinjaError):
    def __init__(self):
        self.message = "unconstrained ip"
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


class ModelError(SENinjaError):
    def __init__(self, model_name, msg):
        self.model_name = model_name
        self.message = "%s: %s" % (model_name, msg)
        super().__init__(self.message)

    def is_fatal(self):
        return True


class UnimplementedInstruction(SENinjaError):
    def __init__(self, instr_name, ip):
        self.instr_name = instr_name
        self.message = "%s instruction is unimplemented @ %#x" % (instr_name, ip)
        super().__init__(self.message)

    def is_fatal(self):
        return True


class UnimplementedModel(SENinjaError):
    def __init__(self, f_name):
        self.f_name = f_name
        self.message = "unimplemented model for function %s" % f_name
        super().__init__(self.message)

    def is_fatal(self):
        return True


class UnimplementedSyscall(SENinjaError):
    def __init__(self, syscall_n):
        self.syscall_n = syscall_n
        self.message = "unimplemented syscall %d" % syscall_n
        super().__init__(self.message)

    def is_fatal(self):
        return True


class UnsupportedOs(SENinjaError):
    def __init__(self, platform_name):
        self.platform_name = platform_name
        self.message = "unsupported os %s" % platform_name
        super().__init__(self.message)

    def is_fatal(self):
        return True


class UnsupportedArch(SENinjaError):
    def __init__(self, arch_name):
        self.arch_name = arch_name
        self.message = "unsupported arch %s" % arch_name
        super().__init__(self.message)

    def is_fatal(self):
        return True
# *****


class SENinjaExeption(Exception):
    pass


class ExitException(SENinjaExeption):
    pass
