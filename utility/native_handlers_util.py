import z3

def __is_hex(v):
    try:
        int(v, 16)
        return True
    except:
        return False

def __find_address_mem(state, parameter):  # hackish way of parsing a mem address. bad, bad, bad code
    assert "[" in parameter and "]" in parameter
    parameter = parameter[parameter.find("[")+1:]
    parameter = parameter[:parameter.find("]")]

    res = None
    parameter = parameter.split("+")
    for sub in parameter:

        m_res  = None
        m_subs = sub.split("*")
        for m_sub in m_subs:
            if state.regs.has_reg(m_sub):
                v = getattr(state.regs, m_sub)
                m_res = v if m_res is None else (m_res * v)
            elif __is_hex(m_sub):
                v = z3.BitVecVal(int(m_sub, 16), state.arch.bits())
                m_res = v if m_res is None else (m_res * v)
            else:
                raise Exception("Unknown subexpression")
        
        res = m_res if res is None else (res + m_res)
    
    return res

def get_src(state, parameter: str, size: int):
    if state.regs.has_reg(parameter):
        res = getattr(state.regs, parameter)
        assert res.size() // 8 == size
        return res
    
    addr = __find_address_mem(state, parameter)
    return state.mem.load(addr, size, state.arch.endness())

def store_to_dst(state, parameter: str, value):
    if state.regs.has_reg(parameter):
        setattr(state.regs, parameter, value)
        return
    
    assert "[" in parameter and "]" in parameter
    parameter = parameter[parameter.find("[")+1:]
    parameter = parameter[:parameter.find("]")]

    parameter = parameter.split("+")

    addr = __find_address_mem(state, parameter)
    return state.mem.store(addr, value, state.arch.endness())