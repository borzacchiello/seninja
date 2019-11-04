from arch.arch_x86_sph import ArchX86SPH
from utility.x86_native_handlers_util import (
    get_src, store_to_dst
)
from utility.z3_wrap_util import split_bv_in_list
import z3

class ArchX8664SPH(ArchX86SPH):
    def __init__(self):
        pass

    # --- AVX2 ---
    def vmovdqu_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]

        src = get_src(sv.state, src_p)
        store_to_dst(sv.state, dst_p, src)

        return True

    def vpmaddubsw_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src1_bytes = split_bv_in_list(src1, 8)
        src2 = get_src(sv.state, src2_p)
        src2_bytes = split_bv_in_list(src2, 8)

        res = None
        for i in range(0, 32, 2):
            a1 = z3.ZeroExt(8, src1_bytes[i])
            a2 = z3.ZeroExt(8, src1_bytes[i+1])
            b1 = z3.SignExt(8, src2_bytes[i])
            b2 = z3.SignExt(8, src2_bytes[i+1])

            w1 = z3.simplify(a1 * b1)
            w2 = z3.simplify(a2 * b2)

            res = z3.simplify(
                w1 + w2
            ) if res is None else z3.simplify(
                z3.Concat(
                    w1 + w2, res
                )
            )
        
        store_to_dst(sv.state, dst_p, res)
        return True

    def vpmaddwd_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src1_words = split_bv_in_list(src1, 16)
        src2 = get_src(sv.state, src2_p)
        src2_words = split_bv_in_list(src2, 16)

        res = None
        for i in range(0, 16, 2):
            a1 = z3.SignExt(16, src1_words[i])
            a2 = z3.SignExt(16, src1_words[i+1])
            b1 = z3.SignExt(16, src2_words[i])
            b2 = z3.SignExt(16, src2_words[i+1])

            d1 = z3.simplify(a1 * b1)
            d2 = z3.simplify(a2 * b2)

            res = z3.simplify(
                d1 + d2
            ) if res is None else z3.simplify(
                z3.Concat(
                    d1 + d2, res
                )
            )
        
        store_to_dst(sv.state, dst_p, res)
        return True

    def vpxor_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = z3.simplify(src1 ^ src2)

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpor_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = z3.simplify(src1 | src2)

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpand_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = z3.simplify(src1 & src2)

        store_to_dst(sv.state, dst_p, res)
        return True
    # ------------