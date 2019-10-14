import z3

def __is_hex(v):
    try:
        int(v, 16)
        return True
    except:
        return False

def get_src(state, parameter: str, size: int):
    if state.regs.has_reg(parameter):
        res = getattr(state.regs, parameter)
        assert res.size() // 8 == size
        return res
    
    assert "[" in parameter and "]" in parameter
    parameter = parameter[parameter.find("[")+1:]
    parameter = parameter[:parameter.find("]")]

    parameter = parameter.split("+")

    res = None
    for sub in parameter:
        if state.regs.has_reg(sub):
            v = getattr(state.regs, sub)
            res = v if res is None else (res + v)
        elif __is_hex(sub):
            v = z3.BitVecVal(int(sub, 16), state.arch.bits())
            res = v if res is None else (res + v)
        else:
            raise Exception("Unknown subexpression")
    
    return state.mem.load(res, size, state.arch.endness())

def store_to_dst(state, parameter: str, value):
    if state.regs.has_reg(parameter):
        setattr(state.regs, parameter, value)
        return
    
    assert "[" in parameter and "]" in parameter
    parameter = parameter[parameter.find("[")+1:]
    parameter = parameter[:parameter.find("]")]

    parameter = parameter.split("+")

    res = None
    for sub in parameter:
        if state.regs.has_reg(sub):
            v = getattr(state.regs, sub)
            res = v if res is None else (res + v)
        elif __is_hex(sub):
            v = z3.BitVecVal(int(sub, 16), state.arch.bits())
            res = v if res is None else (res + v)
        else:
            raise Exception("Unknown subexpression")
    
    return state.mem.store(res, value, state.arch.endness())
