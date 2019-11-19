from expr import BVV

_size_dict = {
    "byte":     1,
    "word":     2,
    "dword":    4,
    "qword":    8,
    "xmmword": 16,
    "ymmword": 32,
    "zmmword": 64
}

def __is_hex(v):
    try:
        int(v, 16)
        return True
    except:
        return False

def __find_address_mem(state, parameter):  # hackish way of parsing a mem address. bad, bad, bad code    
    assert "[" in parameter and "]" in parameter

    size = parameter[:parameter.find("[")]
    size = size.replace(" ", "")
    size = _size_dict[size]

    parameter = parameter.replace("rel", "")
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
                v = BVV(int(m_sub, 16), state.arch.bits())
                m_res = v if m_res is None else (m_res * v)
            else:
                raise Exception("Unknown subexpression")
        
        res = m_res if res is None else (res + m_res)
    
    return res, size

def get_src(state, parameter: str):
    if state.regs.has_reg(parameter):
        res = getattr(state.regs, parameter)
        return res
    
    addr, size = __find_address_mem(state, parameter)
    return state.mem.load(addr, size, state.arch.endness())

def store_to_dst(state, parameter: str, value):
    if state.regs.has_reg(parameter):
        setattr(state.regs, parameter, value)
        return
    
    assert "[" in parameter and "]" in parameter

    addr, _ = __find_address_mem(state, parameter)
    return state.mem.store(addr, value, state.arch.endness())
