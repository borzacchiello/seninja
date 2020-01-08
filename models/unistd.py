from ..utility.expr_wrap_util import symbolic
from ..expr import BVV, BVS
from ..utility.models_util import get_arg_k
from ..sym_state import State

MAX_READ = 100

def read_handler(state: State, view):
    fd    = get_arg_k(state, 1, 4, view)
    buf   = get_arg_k(state, 2, state.arch.bits() // 8, view)
    count = get_arg_k(state, 3, 4, view)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.value
    assert state.os.is_open(fd)
    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.value
    
    s = "read_fd%d" % fd
    for i in range(count):
        b = BVS(s + "_%d" % i, 8)
        state.os.get_device_by_fd(fd).append(b)
        state.mem.store(buf + i, b)
    
    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return BVV(count, 32)

def write_handler(state: State, view):
    fd    = get_arg_k(state, 1, 4, view)
    buf   = get_arg_k(state, 2, state.arch.bits() // 8, view)
    count = get_arg_k(state, 3, 4, view)

    assert not symbolic(fd) or not state.solver.symbolic(fd)
    fd = fd.value
    if symbolic(count):
        count = state.solver.max(count)
        count = MAX_READ if count > MAX_READ else count
    else:
        count = count.value
    
    for i in range(count):
        b = state.mem.load(buf + i, 1)
        state.os.get_device_by_fd(fd).append(b)
    
    state.events.append(
        "read from fd %d, count %d" % (fd, count)
    )
    return BVV(count, 32)

stat_idx = 0
def _stat(state: State, statbuf):
    global stat_idx

    long_t  = state.arch.bits()
    int_t   = 32

    st_dev          = BVS('stat_st_dev_%d' % stat_idx,     long_t)
    st_ino          = BVS('stat_st_ino_%d' % stat_idx,     long_t)
    st_mode         = BVS('stat_st_mode_%d' % stat_idx,    long_t)
    st_nlink        = BVS('stat_st_nlink_%d' % stat_idx,   long_t)
    st_uid          = BVS('stat_st_uid_%d' % stat_idx,     int_t )
    st_gid          = BVS('stat_st_gid_%d' % stat_idx,     int_t )
    st_rdev         = BVS('stat_st_rdev_%d' % stat_idx,    long_t)
    st_size         = BVS('stat_st_size_%d' % stat_idx,    long_t)
    st_blksize      = BVS('stat_st_blksize_%d' % stat_idx, long_t)
    st_blocks       = BVS('stat_st_blocks_%d' % stat_idx,  long_t)
    st_atim_tv_sec  = BVS('stat_atim.sec_%d' % stat_idx,   long_t)
    st_atim_tv_nsec = BVS('stat_atim.nsec_%d' % stat_idx,  long_t)
    st_mtim_tv_sec  = BVS('stat_mtim.sec_%d' % stat_idx,   long_t)
    st_mtim_tv_nsec = BVS('stat_mtim.nsec_%d' % stat_idx,  long_t)
    st_ctim_tv_sec  = BVS('stat_ctim.sec_%d' % stat_idx,   long_t)
    st_ctim_tv_nsec = BVS('stat_ctim.nsec_%d' % stat_idx,  long_t)

    stat_idx += 1

    state.mem.store(statbuf +   0, st_dev,          state.arch.endness())
    state.mem.store(statbuf +   8, st_ino,          state.arch.endness())
    state.mem.store(statbuf +  16, st_nlink,        state.arch.endness())
    state.mem.store(statbuf +  24, st_mode,         state.arch.endness())
    state.mem.store(statbuf +  32, st_uid,          state.arch.endness())
    state.mem.store(statbuf +  36, st_gid,          state.arch.endness())
    state.mem.store(statbuf +  40, BVV(0, 8*8))  # padding
    state.mem.store(statbuf +  48, st_rdev,         state.arch.endness())
    state.mem.store(statbuf +  56, st_size,         state.arch.endness())
    state.mem.store(statbuf +  64, st_blksize,      state.arch.endness())
    state.mem.store(statbuf +  72, st_blocks,       state.arch.endness())
    state.mem.store(statbuf +  80, st_atim_tv_sec,  state.arch.endness())
    state.mem.store(statbuf +  88, st_atim_tv_nsec, state.arch.endness())
    state.mem.store(statbuf +  96, st_mtim_tv_sec,  state.arch.endness())
    state.mem.store(statbuf + 104, st_mtim_tv_nsec, state.arch.endness())
    state.mem.store(statbuf + 112, st_ctim_tv_sec,  state.arch.endness())
    state.mem.store(statbuf + 120, st_ctim_tv_nsec, state.arch.endness())
    state.mem.store(statbuf + 128, BVV(0, 8*16)) # reserved (zero (?))

    return BVV(0, 32)

def stat_handler(state: State, view):
    global stat_idx

    pathname = get_arg_k(state, 1, state.arch.bits() // 8, view)
    statbuf  = get_arg_k(state, 2, state.arch.bits() // 8, view)

    path = ""
    if not symbolic(pathname):
        i = 0
        c = state.mem.load(pathname, 1)
        while not symbolic(c) and c.value != 0 and i < 100:
            path += chr(c.value)
            i += 1
            c = state.mem.load(pathname+i, 1)
    else:
        path = "<symbolic>"

    state.events.append(
        "stat on %s" % path
    )

    return _stat(state, statbuf)

def xstat_handler(state: State, view):
    version  = get_arg_k(state, 1, 4, view)
    pathname = get_arg_k(state, 2, state.arch.bits() // 8, view)
    statbuf  = get_arg_k(state, 3, state.arch.bits() // 8, view)

    path = ""
    if not symbolic(pathname):
        i = 0
        c = state.mem.load(pathname, 1)
        while not symbolic(c) and c.value != 0 and i < 100:
            path += chr(c.value)
            i += 1
            c = state.mem.load(pathname+i, 1)
    else:
        path = "<symbolic>"
    
    if not symbolic(version):
        version = str(version.value)
    else:
        version = "<symbolic>"

    state.events.append(
        "__xstat on %s. version %s" % (path, version)
    )

    return _stat(state, statbuf)
