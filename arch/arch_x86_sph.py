from ..utility.bninja_util import get_function, get_addr_next_inst
from ..utility.x86_native_handlers_util import (
    store_to_dst, get_src
)
from ..expr import ITE, BVV
from .arch_abstract import SpecialInstructionHandler

class ArchX86SPH(SpecialInstructionHandler):
    def __init__(self):
        pass

    def _setCC(self, sv, parameters):
        func = get_function(sv.view, sv.ip)
        expr = func.llil[sv.llil_ip]
        if expr.operation.name != "LLIL_IF":
            return False
        
        # we have cmp/test + setCC. Avoid fork
        cond = sv.visit(expr.condition)

        v = ITE(cond, BVV(1, 8), BVV(0, 8))
        store_to_dst(sv.state, parameters[0], v)

        sv._wasjmp = True
        sv.update_ip(
            func, 
            func.llil.get_instruction_start(
                get_addr_next_inst(sv.view, sv.ip))
        )
        return True

    def seta_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setae_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setb_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setbe_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setc_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def sete_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setg_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setge_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setl_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setle_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setna_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnae_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnb_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnbe_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnc_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setne_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setng_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnge_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnl_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnle_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setno_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnp_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setns_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setnz_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def seto_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setp_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setpe_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setpo_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def sets_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    def setz_handler(self, sv, parameters):
        return self._setCC(sv, parameters)
    
    def paddb_handler(self, sv, parameters):
        return False

    def paddw_handler(self, sv, parameters):
        return False

    def paddd_handler(self, sv, parameters):
        return False

    def paddq_handler(self, sv, parameters):
        return False

    def paddsb_handler(self, sv, parameters):
        return False

    def paddsw_handler(self, sv, parameters):
        return False

    def paddsd_handler(self, sv, parameters):
        return False

    def paddsq_handler(self, sv, parameters):
        return False

    # ----- mmx -----
    def movd_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]

        # get src (32bit)
        src = get_src(sv.state, src_p)
        assert src.size == 32

        store_to_dst(sv.state, dst_p, src.ZeroExt(16*8-32))
        return True

    def movq_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]

        # get src (64bit)
        src = get_src(sv.state, src_p)
        assert src.size == 64

        store_to_dst(sv.state, dst_p, src.ZeroExt(16*8-64))
        return True
    # ----------------