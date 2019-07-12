from models.libc import *

library_functions = {
    'printf':           printf_handler,
    'scanf':            scanf_handler,
    '__isoc99_scanf':   scanf_handler,
    'strcmp':           strcmp_handler,
    'strlen':           strlen_handler,
    'atoi':             atoi_handler
}
