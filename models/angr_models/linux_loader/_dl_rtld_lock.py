from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES


class _dl_rtld_lock_recursive(FakeSimProcedure):
    # pylint: disable=arguments-differ, unused-argument
    def run(self, lock):
        # For future reference:
        # ++((pthread_mutex_t *)(lock))->__data.__count;
        return

class _dl_rtld_unlock_recursive(FakeSimProcedure):
    def run(self):
        return
