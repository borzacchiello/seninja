from utility.z3_wrap_util import symbolic, bvs, bvv

MAX_READ = 100

def read_handler(state):
    fd_reg    = state.os.get_syscall_parameter(1)
    buf_reg   = state.os.get_syscall_parameter(2)
    count_reg = state.os.get_syscall_parameter(3)

    fd    = getattr(state.regs, fd_reg)
    buf   = getattr(state.regs, buf_reg)
    count = getattr(state.regs, count_reg)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.as_long()
    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.as_long()
    
    s = "read_fd%d" % fd
    for i in range(count):
        b = bvs(s + "_%d" % i, 8)
        state.os.get_stdin().append(b)
        state.mem.store(buf + i, b)
    
    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return bvv(count, 32)

def write_handler(state):
    fd_reg    = state.os.get_syscall_parameter(1)
    buf_reg   = state.os.get_syscall_parameter(2)
    count_reg = state.os.get_syscall_parameter(3)

    fd    = getattr(state.regs, fd_reg)
    buf   = getattr(state.regs, buf_reg)
    count = getattr(state.regs, count_reg)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.as_long()
    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.as_long()
    
    for i in range(count):
        b = state.mem.load(buf + i, 1)
        state.os.get_device_by_fd(fd).append(b)
    
    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return bvv(count, 32)

def exit_handler(state):
    pass
