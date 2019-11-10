from utility.z3_wrap_util import symbolic, bvs, bvv
from utility.models_util import get_arg_k
from sym_state import State

MAX_READ = 100

def read_handler(state: State, view):
    fd    = get_arg_k(state, 1, 4, view)
    buf   = get_arg_k(state, 2, state.arch.bits() // 8, view)
    count = get_arg_k(state, 3, 4, view)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.as_long()
    assert state.os.is_open(fd)
    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.as_long()
    
    s = "read_fd%d" % fd
    for i in range(count):
        b = bvs(s + "_%d" % i, 8)
        state.os.get_device_by_fd(fd).append(b)
        state.mem.store(buf + i, b)
    
    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return bvv(count, 32)

def write_handler(state: State, view):
    fd    = get_arg_k(state, 1, 4, view)
    buf   = get_arg_k(state, 2, state.arch.bits() // 8, view)
    count = get_arg_k(state, 3, 4, view)

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
