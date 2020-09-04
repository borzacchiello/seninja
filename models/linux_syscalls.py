from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS

MAX_READ = 100


def read_handler(state):
    fd_reg = state.os.get_syscall_parameter(1)
    buf_reg = state.os.get_syscall_parameter(2)
    count_reg = state.os.get_syscall_parameter(3)

    fd = getattr(state.regs, fd_reg)
    buf = getattr(state.regs, buf_reg)
    count = getattr(state.regs, count_reg)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.value
    assert state.os.is_open(fd)

    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.value

    res = state.os.read(fd, count)
    for i, b in enumerate(res):
        state.mem.store(buf + i, b)

    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return BVV(count, 32)


def write_handler(state):
    fd_reg = state.os.get_syscall_parameter(1)
    buf_reg = state.os.get_syscall_parameter(2)
    count_reg = state.os.get_syscall_parameter(3)

    fd = getattr(state.regs, fd_reg)
    buf = getattr(state.regs, buf_reg)
    count = getattr(state.regs, count_reg)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.value
    assert state.os.is_open(fd)

    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.value

    data = []
    for i in range(count):
        b = state.mem.load(buf + i, 1)
        data.append(b)
    state.os.write(fd, data)

    state.events.append(
        "write to fd %d, count %d" % (fd, count)
    )
    return BVV(count, 32)


def exit_handler(state):
    pass
