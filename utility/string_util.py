def str_to_int(s):
    res = ""
    for c in s:
        res += hex(ord(c))[2:]
    res += "00"
    return int(res, 16)

def int_to_str(i):
    s = hex(i)[2:]
    res = ""
    for i in range(0, len(s), 2):
        res += chr(int(s[i] + s[i+1], 16))
    return res
