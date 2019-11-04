from arch.arch_abstract import SpecialInstructionHandler
from utility.bninja_util import get_function, get_addr_next_inst
from utility.x86_native_handlers_util import (
    store_to_dst, get_src
)
import z3

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

        v = z3.If(cond, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8))
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
