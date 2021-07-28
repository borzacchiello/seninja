from .. import FakeSimProcedure, FakeSimProcedureError, claripy, FakeOptions
from ..procedures_dict import SIM_PROCEDURES

# pylint: disable=unused-argument,arguments-differ

class _dl_vdso_vsym(FakeSimProcedure):
    def run(self, name, vers):
        return 0
        #namestr = self.state.mem[name].string.concrete
        #if namestr.startswith('_vdso_'):
        #    realname = namestr[6:]
        #    lib = angr.SIM_LIBRARIES['linux_kernel']
        #else:
        #    raise FakeSimProcedureError('_dl_vdso_vsym(%r): unsupported' % namestr)

        #addr = self.project.loader.extern_object.get_pseudo_addr(realname)
        #if not self.project.is_hooked(addr):
        #    self.project.hook(addr, lib.get(realname, self.arch))
        #return addr
