from ..expr import BVS, BVV
from ..os_models.windows import Windows


def test_1():
    l = Windows()
    l.write(0, [BVV(0xaa, 8), BVV(0xbb, 8), BVV(0xcc, 8)])

    res = l.get_stdin_stream()
    assert len(res) == 3
    assert (
        isinstance(res[0], BVV) and
        isinstance(res[1], BVV) and
        isinstance(res[2], BVV)
    )
    assert (
        res[0].value == 0xaa and
        res[1].value == 0xbb and
        res[2].value == 0xcc
    )


def test_2():
    l = Windows()
    l.write(1, [BVV(0xaa, 8), BVV(0xbb, 8), BVV(0xcc, 8)])

    res = l.get_stdout_stream()
    assert len(res) == 3
    assert (
        isinstance(res[0], BVV) and
        isinstance(res[1], BVV) and
        isinstance(res[2], BVV)
    )
    assert (
        res[0].value == 0xaa and
        res[1].value == 0xbb and
        res[2].value == 0xcc
    )


def test_3():
    l = Windows()
    assert l.stdin_fd == 0
    assert l.stdout_fd == 1


def test_4():
    l1 = Windows()
    l1.write(0, [BVV(0xaa, 8)])

    l2 = l1.copy(None)

    l2.write(0, [BVV(0xbb, 8)])

    res1 = l1.get_stdin_stream()
    res2 = l2.get_stdin_stream()

    assert len(res1) == 1
    assert isinstance(res1[0], BVV)
    assert res1[0].value == 0xaa

    assert len(res2) == 2
    assert (
        isinstance(res2[0], BVV) and
        isinstance(res2[1], BVV)
    )
    assert (
        res2[0].value == 0xaa and
        res2[1].value == 0xbb
    )
