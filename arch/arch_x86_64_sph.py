from .arch_x86_sph import ArchX86SPH
from ..utility.x86_native_handlers_util import (
    get_src, store_to_dst
)
from ..utility.expr_wrap_util import split_bv_in_list
from ..expr import BVArray, ITE, BVV


class ArchX8664SPH(ArchX86SPH):
    def __init__(self):
        self._vpermd_idx = 0
        self._vpshufb_idx = 0

    def cpuid_handler(self, sv, parameters):
        return self.cpuid_util(sv, 64)

    def xgetbv_handler(self, sv, parameters):
        sv.state.regs.rax = BVV(7, 64)
        sv.state.regs.rdx = BVV(0, 64)
        return True

    # --- AVX2 ---
    def vmovdqu_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]

        src = get_src(sv.state, src_p)
        store_to_dst(sv.state, dst_p, src)

        return True

    def vpmaddubsw_handler(self, sv, parameters):
        dst_p = parameters[0]
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
        dst_p = parameters[0]
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

    def vpaddd_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src1_dwords = split_bv_in_list(src1, 32)
        src2 = get_src(sv.state, src2_p)
        src2_dwords = split_bv_in_list(src2, 32)

        res = None
        for i in range(32 // 4):
            res = (
                src1_dwords[i] + src2_dwords[i]
            ) if res is None else (
                (src1_dwords[i] + src2_dwords[i]).Concat(
                    res
                )
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpaddb_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src1_bytes = split_bv_in_list(src1, 8)
        src2 = get_src(sv.state, src2_p)
        src2_bytes = split_bv_in_list(src2, 8)

        res = None
        for i in range(32):
            res = (
                src1_bytes[i] + src2_bytes[i]
            ) if res is None else (
                (src1_bytes[i] + src2_bytes[i]).Concat(
                    res
                )
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpxor_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = src1 ^ src2

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpor_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = src1 | src2

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpand_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src2 = get_src(sv.state, src2_p)

        res = src1 & src2

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpermd_handler(self, sv, parameters):
        dst_p = parameters[0]
        idx_p = parameters[1]
        src_p = parameters[2]

        # get src and store it in a BVArray
        src = get_src(sv.state, src_p)
        src_dwords = split_bv_in_list(src, 32)
        assert len(src_dwords) == 8
        array_src = BVArray(
            "vpermd_array_{}".format(self._vpermd_idx),
            3,
            32
        )
        for i in range(8):
            array_src.Store(i, src_dwords[i])

        # get idx
        idx = get_src(sv.state, idx_p)
        idx_dwords = split_bv_in_list(idx, 32)

        # compute permutation
        res = None
        for idx in idx_dwords:
            idx_value = idx.Extract(2, 0)
            res = (
                array_src.Select(idx_value)
            ) if res is None else (
                array_src.Select(idx_value).Concat(
                    res
                )
            )

        # save result
        store_to_dst(sv.state, dst_p, res)

        self._vpermd_idx += 1
        return True

    def vpshufb_handler(self, sv, parameters):
        dst_p = parameters[0]
        idx_p = parameters[2]
        src_p = parameters[1]

        src = get_src(sv.state, src_p)
        src_bytes = split_bv_in_list(src, 8)
        idx = get_src(sv.state, idx_p)
        idx_bytes = split_bv_in_list(idx, 8)

        array_src_low = BVArray(
            "vpshufb_array_low_{}".format(self._vpshufb_idx),
            4,
            8
        )
        for i in range(16):
            array_src_low.Store(i, src_bytes[i])

        array_src_hig = BVArray(
            "vpshufb_array_hig_{}".format(self._vpshufb_idx),
            4,
            8
        )
        for i in range(16, 32):
            array_src_hig.Store(i, src_bytes[i])

        idx_bytes_low = idx_bytes[:16]
        idx_bytes_hig = idx_bytes[16:]

        res = None
        for idx in idx_bytes_low:
            idx_low4 = idx.Extract(3, 0)
            val = ITE(
                idx.Extract(7, 7) == 0,
                array_src_low.Select(idx_low4),
                BVV(0, 8)
            )
            res = (
                val
            ) if res is None else (
                val.Concat(
                    res
                )
            )
        for idx in idx_bytes_hig:
            idx_low4 = idx.Extract(3, 0)
            val = ITE(
                idx.Extract(7, 7) == 0,
                array_src_hig.Select(idx_low4),
                BVV(0, 8)
            )
            res = val.Concat(res)

        # save result
        store_to_dst(sv.state, dst_p, res)

        self._vpshufb_idx += 1
        return True

    def vpsrld_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]
        count_p = parameters[2]

        src = get_src(sv.state, src_p)
        src_dwords = split_bv_in_list(src, 32)

        count = get_src(sv.state, count_p)
        count = count.Extract(31, 0)

        res = None
        for dw in src_dwords:
            res = (
                dw.LShR(count)
            ) if res is None else(
                dw.LShR(count).Concat(
                    res
                )
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpslld_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]
        count_p = parameters[2]

        src = get_src(sv.state, src_p)
        src_dwords = split_bv_in_list(src, 32)

        count = get_src(sv.state, count_p)
        count = count.Extract(31, 0)

        res = None
        for dw in src_dwords:
            res = (
                dw.LShL(count)
            ) if res is None else (
                dw.LShL(count).Concat(
                    res
                )
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpcmpeqb_handler(self, sv, parameters):
        dst_p = parameters[0]
        src1_p = parameters[1]
        src2_p = parameters[2]

        src1 = get_src(sv.state, src1_p)
        src1_bytes = split_bv_in_list(src1, 8)
        src2 = get_src(sv.state, src2_p)
        src2_bytes = split_bv_in_list(src2, 8)

        res = None
        for i in range(32):
            val = ITE(
                src1_bytes[i] == src2_bytes[i],
                BVV(0xff, 8),
                BVV(0x00, 8)
            )
            res = (
                val
            ) if res is None else (
                val.Concat(
                    res
                )
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    def vpmovmskb_handler(self, sv, parameters):
        dst_p = parameters[0]
        src_p = parameters[1]

        src = get_src(sv.state, src_p)
        src_bytes = split_bv_in_list(src, 8)

        res = None
        for i in range(32):
            val = src_bytes[i].Extract(7, 7)
            res = (
                val
            ) if res is None else (
                val.Concat(res)
            )

        store_to_dst(sv.state, dst_p, res)
        return True

    # ------------
