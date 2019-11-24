import models.others as models_other
import models.libc as models_libc
import models.unistd as models_unistd
import models.string as models_string
import models.teensy as models_teensy

library_functions = {
    'printf':           models_libc.printf_handler,
    'scanf':            models_libc.scanf_handler,
    '__isoc99_scanf':   models_libc.scanf_handler,
    'getchar':          models_libc.getchar_handler,
    'strcmp':           models_libc.strcmp_handler,
    'strlen':           models_libc.strlen_handler,
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

    # models Teensy Board
    '_ZN5Print7printlnEi': models_teensy.println_handler  
}
