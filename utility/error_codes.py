from enum import Enum

class ErrorInstruction(Enum):
    DIVISION_BY_ZERO = 0
    UNMAPPED_READ    = 1
    UNMAPPED_WRITE   = 2
