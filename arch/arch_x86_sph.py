from ..utility.bninja_util import (
    get_function, get_addr_next_inst
)
from ..utility.x86_native_handlers_util import (
    store_to_dst, get_src
)
from ..utility.expr_wrap_util import split_bv_in_list
from ..utility.exceptions import ModelError
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

        return True

    def cpuid_util(self, sv, bits):
        dst_eax = 'eax' if bits == 32 else 'rax'
        dst_ebx = 'ebx' if bits == 32 else 'rbx'
        dst_ecx = 'ecx' if bits == 32 else 'rcx'
        dst_edx = 'edx' if bits == 32 else 'rdx'

        eax_v = sv.state.regs.eax
        ecx_v = sv.state.regs.ecx
        if not isinstance(eax_v, BVV):
            raise ModelError("cpuid", "symbolic eax")
        if not isinstance(ecx_v, BVV):
            raise ModelError("cpuid", "symbolic ecx")
        eax_v = eax_v.value
        ecx_v = ecx_v.value
        if eax_v == 0 and ecx_v == 0:
            setattr(sv.state.regs, dst_eax, BVV(0x00000010, bits))
            setattr(sv.state.regs, dst_ebx, BVV(0x68747541, bits))
            setattr(sv.state.regs, dst_ecx, BVV(0x444d4163, bits))
            setattr(sv.state.regs, dst_edx, BVV(0x69746e65, bits))
        elif eax_v == 1 and ecx_v == 0:
            setattr(sv.state.regs, dst_eax, BVV(0x00870f10, bits))
            setattr(sv.state.regs, dst_ebx, BVV(0x000c0800, bits))
            setattr(sv.state.regs, dst_ecx, BVV(0x7ed8320b, bits))
            setattr(sv.state.regs, dst_edx, BVV(0x178bfbff, bits))
        elif eax_v == 7 and ecx_v == 0:
            setattr(sv.state.regs, dst_eax, BVV(0x00000000, bits))
            setattr(sv.state.regs, dst_ebx, BVV(0x219c91a9, bits))
            setattr(sv.state.regs, dst_ecx, BVV(0x00400004, bits))
            setattr(sv.state.regs, dst_edx, BVV(0x00000000, bits))
        else:
            raise ModelError(
                "cpuid", "unsupported (eax, ecx) value (%d, %d)" % (eax_v, ecx_v))

        return True

    def cpuid_handler(self, sv, parameters):
        return self.cpuid_util(sv, 32)

    def xgetbv_handler(self, sv, parameters):
        sv.state.regs.eax = BVV(7, 32)
        sv.state.regs.edx = BVV(0, 32)
        return True

    def paddb_handler(self, sv, parameters):
        src1 = get_src(sv.state, parameters[0])
        src1_bytes = split_bv_in_list(src1, 8)
        src2 = get_src(sv.state, parameters[1])
        src2_bytes = split_bv_in_list(src2, 8)

        res = None
        for b1, b2 in zip(src1_bytes, src2_bytes):
            if res is None:
                res = b1 + b2
            else:
                res = (b1 + b2).Concat(res)

        store_to_dst(sv.state, parameters[0], res)
        return True

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
        if src.size > 64:
            src = src.Extract(63, 0)

        if "[" not in dst_p:
            store_to_dst(sv.state, dst_p, src.ZeroExt(16*8-64))
        else:
            store_to_dst(sv.state, dst_p, src)
        return True
    # ----------------
