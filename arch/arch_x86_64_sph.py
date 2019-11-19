from arch.arch_x86_sph import ArchX86SPH
from utility.x86_native_handlers_util import (
    get_src, store_to_dst
)
from utility.expr_wrap_util import split_bv_in_list

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
            a1 = src1_bytes[i].ZeroExt(8)
            a2 = src1_bytes[i+1].ZeroExt(8)
            b1 = src2_bytes[i].SignExt(8)
            b2 = src2_bytes[i+1].SignExt(8)

            w1 = a1 * b1
            w2 = a2 * b2

            res = (
                w1 + w2
            ) if res is None else (
                (w1 + w2).Concat(
                    res
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
            a1 = src1_words[i].SignExt(16)
            a2 = src1_words[i+1].SignExt(16)
            b1 = src2_words[i].SignExt(16)
            b2 = src2_words[i+1].SignExt(16)

            d1 = a1 * b1
            d2 = a2 * b2

            res = (
                d1 + d2
            ) if res is None else (
                (d1 + d2).Concat(
                    res
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

        res = src1 ^ src2

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpor_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = src1 | src2

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpand_handler(self, sv, parameters):
        dst_p  = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = src1 & src2

        store_to_dst(sv.state, dst_p, res)
        return True
    # ------------