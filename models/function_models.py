import models.libc as models_libc
import models.unistd as models_unistd

library_functions = {
    'printf':           models_libc.printf_handler,
    'scanf':            models_libc.scanf_handler,
    '__isoc99_scanf':   models_libc.scanf_handler,
    'strcmp':           models_libc.strcmp_handler,
    'strlen':           models_libc.strlen_handler,
    'atoi':             models_libc.atoi_handler,
    'malloc':           models_libc.malloc_handler,
    'read':             models_unistd.read_handler,
    'write':            models_unistd.write_handler
}
