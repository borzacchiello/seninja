from ..expr import BVV
from ..memory.sym_flat_memory_not_paged import MemoryConcreteFlatNotPaged


def test_1():
    m1 = MemoryConcreteFlatNotPaged("")
    m1.store(BVV(0, m1.bits), BVV(0xff, 8))

    m2 = m1.copy()

    assert id(m1.values) == id(m2.values)

    m2.store(BVV(1, m2.bits), BVV(0xfa, 8))

    r11 = m1.load(BVV(0, m1.bits), 1)
    r12 = m1.load(BVV(1, m1.bits), 1)

    r21 = m2.load(BVV(0, m2.bits), 1)
    r22 = m2.load(BVV(1, m2.bits), 1)

    assert isinstance(r11, BVV)
    assert r11.value == 0xff
    assert not isinstance(r12, BVV)

    assert isinstance(r21, BVV)
    assert r21.value == 0xff
    assert isinstance(r22, BVV)
    assert r22.value == 0xfa
