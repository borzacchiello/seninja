from .error_codes import ErrorInstruction


def check_unsupported(val, expr):
    if val is None:
        raise Exception("unsupported instruction '%s'" % (expr.operation.name))


def check_error(val):
    return isinstance(val, ErrorInstruction)
