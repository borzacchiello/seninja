from ..expr import BVS, BVV
from ..memory.sym_file import SymFile
from ..os_models.os_file import OsFileHandler

def test_1():  # read unconstrained
    f = SymFile("a")
    res = f.read(1)
    assert len(res) == 1
    assert isinstance(res[0], BVS)
    assert res[0].name == "unconstrained_a_0"

def test_2():  # read concrete
    f = SymFile("a")
    f.write([BVV(0xff, 8)])
    f.seek(0)
    res = f.read(1)
    assert len(res) == 1
    assert isinstance(res[0], BVV)
    assert res[0].value == 255

def test_3():
    os = OsFileHandler()
    fd = os.open("stdin", "r--")
    assert fd == 0

def test_4():
    os = OsFileHandler()
    fd = os.open("stdin", "r--")
    
    assert os.is_open(fd)
    os.close(fd)
    assert not os.is_open(fd)

def test_5():
    os = OsFileHandler()
    fd1 = os.open("A", "-w-")
    fd2 = os.open("A", "r--")
    
    os.write(fd1, [BVV(0xff, 8)])
    res = os.read(fd2, 1)
    
    assert len(res) == 1
    assert isinstance(res[0], BVV)
    assert res[0].value == 255

def test_6():
    os1 = OsFileHandler()
    os2 = OsFileHandler()

    fd1 = os1.open("A", "-w-")
    os1.write(fd1, [BVV(0xff, 8)])
    fd2 = os1.open("A", "r--")

    os1.copy_to(os2)

    res = os2.read(fd2, 1)
    assert len(res) == 1
    assert isinstance(res[0], BVV)
    assert res[0].value == 255
