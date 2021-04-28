from ..expr import BVV, BVS
from . import others as models_other
from . import libc as models_libc
from . import unistd as models_unistd
from . import string as models_string
from . import teensy as models_teensy

def reval_model(val, nbits):
    return lambda state, view: BVV(val, nbits)

library_functions = {
    'printf':           models_libc.printf_handler,
    '__printf_chk':     models_libc.printf_chk_handler,
    'scanf':            models_libc.scanf_handler,
    '__isoc99_scanf':   models_libc.scanf_handler,
    'getchar':          models_libc.getchar_handler,
    'putchar':          models_libc.putchar_handler,
    'puts':             models_libc.puts_handler,
    'fgets':            models_libc.fgets_handler,
    'strcmp':           models_string.strcmp_handler,
    'strlen':           models_string.strlen_handler,
    'strcpy':           models_string.strcpy_handler,
    'strncpy':          models_string.strncpy_handler,
    'isxdigit':         models_libc.isxdigit_handler,
    'atoi':             models_libc.atoi_handler,
    'atol':             models_libc.atol_handler,
    'atoll':            models_libc.atol_handler,
    'malloc':           models_libc.malloc_handler,
    'calloc':           models_libc.calloc_handler,
    'read':             models_unistd.read_handler,
    'write':            models_unistd.write_handler,
    'memcmp':           models_string.memcmp_handler,
    'memset':           models_string.memset_handler,
    'time':             models_other.time_handler,
    'stat':             models_unistd.stat_handler,
    '__xstat':          models_unistd.xstat_handler,
    'exit':             models_libc.exit_handler,

    # concrete models
    'strtoul':          models_libc.strtoul_handler,
    'srand':            models_libc.srand_handler,
    'rand':             models_libc.rand_handler,

    # models Teensy Board
    # Print::println(int)
    '_ZN5Print7printlnEi':   models_teensy.println_handler,
    # Print::println(char*)
    '_ZN5Print7printlnEPKc': models_teensy.println_handler
}
