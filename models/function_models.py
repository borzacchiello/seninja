import models.libc as models

library_functions = {
    'printf':           models.printf_handler,
    'scanf':            models.scanf_handler,
    '__isoc99_scanf':   models.scanf_handler,
    'strcmp':           models.strcmp_handler,
    'strlen':           models.strlen_handler,
    'atoi':             models.atoi_handler,
    'malloc':           models.malloc_handler
}
