from ..utility.bninja_util import get_function, get_addr_next_inst
from ..utility.x86_native_handlers_util import (
    store_to_dst, get_src
)
from ..expr import ITE, BVV, Bool
from .arch_abstract import SpecialInstructionHandler


class ArchX86SPH(SpecialInstructionHandler):
    flag_ops = ['a', 'ae', 'b', 'be', 'c', 'e', 'g', 'ge', 'l',
                'le', 'na', 'ae', 'nb', 'nbe', 'nc', 'ne', 'ng', 'nge',
                'nl', 'nle', 'no', 'np', 'ns', 'nz', 'o', 'p', 'pe',
                'po', 's', 'z']

    def __init__(self):
        setcc_format = "set{fo}_handler"
        cmovcc_format = "cmov{fo}_handler"
        for fo in ArchX86SPH.flag_ops:
            setattr(
                self,
                setcc_format.format(fo=fo),
                lambda sv, parameters: self._setCC(sv, parameters)
            )
            setattr(
                self,
                cmovcc_format.format(fo=fo),
                lambda sv, parameters: self._cmovCC(sv, parameters)
            )

    def _setCC(self, executor, parameters):
        func = executor.bncache.get_function(executor.ip)
        expr = func.llil[executor.llil_ip]
        if expr.operation.name != "LLIL_IF":
            return False

        # we have cmp/test + setCC. Avoid fork
        cond = executor.visitor.visit(expr.condition)
        if not isinstance(cond, Bool):
            assert cond.size == 1
            cond = cond == BVV(1, 1)  # to bool

        v = ITE(cond, BVV(1, 8), BVV(0, 8))
        store_to_dst(executor.state, parameters[0], v)

        executor._wasjmp = True
        executor.update_ip(
            func.name,
            func.llil.get_instruction_start(
                executor.ip + executor.bncache.get_instruction_len(executor.ip)
            )
        )
        return True

    def _cmovCC(self, executor, parameters):
        func = executor.bncache.get_function(executor.ip)
        expr = func.llil[executor.llil_ip]
        if expr.operation.name != "LLIL_IF":
            return False

        # we have cmp/test + cmovCC. Avoid fork
        cond = executor.visitor.visit(expr.condition)
        if not isinstance(cond, Bool):
            assert cond.size == 1
            cond = cond == BVV(1, 1)  # to bool

        new_data = get_src(executor.state, parameters[1])
        old_data = get_src(executor.state, parameters[0])
        cond_data = ITE(cond, new_data, old_data)

        store_to_dst(executor.state, parameters[0], cond_data)

        executor._wasjmp = True
        executor.update_ip(
            func.name,
            func.llil.get_instruction_start(
                executor.ip + executor.bncache.get_instruction_len(executor.ip)
            )
        )
        return True

    def cpuid_handler(self, sv, parameters):
        sv.state.regs.eax = BVV(0x00870f10, 32)
        sv.state.regs.ebx = BVV(0x010c0800, 32)
        sv.state.regs.ecx = BVV(0x7ed8320b, 32)
        sv.state.regs.edx = BVV(0x178bfbff, 32)
        return True

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
