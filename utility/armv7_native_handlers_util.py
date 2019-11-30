from collections import namedtuple
import re

ArmV7Mnemonic = namedtuple("ArmV7Mnemonic",  ["mnemonic", "set_flag", "cond"])
ArmV7RotShift = namedtuple("ArmV7RotShift",  ["type", "size"])

conds = {
    'EQ', 'NE', 'GT', 'LT', 'GE', 'LE', 
    'CS', 'CC', 'LO', 'MI', 'PL', 'AL', 
    'NV', 'VS', 'VC', 'HI', 'LS'
}
shift_rot = {
    'ASR', 'LSL', 'LSR', 'ROR', 'RRX'
}
conds_regex     = '|'.join(map(lambda x: x.lower(), conds))
shift_rot_regex = '|'.join(map(lambda x: x.lower(), shift_rot))

def parse_mnemonic(instr):
    regex_mnemonic = \
        r"^([a-z]+?)"        + \
        r"(s?)"              + \
        r"({conds_regex})?\b"  \
        .format(conds_regex=conds_regex)
    
    res = re.match(regex_mnemonic, instr)
    assert res is not None  # parse failed
    res = res.groups()
    
    return ArmV7Mnemonic(
        mnemonic=res[0],
        set_flag=res[1] != '',
        cond=res[2]
    )

def parse_rot_shift(par):
    regex_rot_shift = r"({shift_rot_regex})\s*\#(0x[0-9]+)".format(
        shift_rot_regex=shift_rot_regex
    )
    tokens = re.match(regex_rot_shift, par)
    assert tokens is not None # parse failed
    tokens = tokens.groups()

    return ArmV7RotShift(
        type=tokens[0],
        size=int(tokens[1], 16) if tokens[1][:2] == '0x' else int(tokens[1])
    )

def parse_immediate(par):
    regex_imm = r"\#(0x[0-9]+)"
    tokens = re.match(regex_imm, par)
    assert tokens is not None # parse failed
    tokens = tokens.groups()

    return int(tokens[0], 16) if tokens[0][:2] == '0x' else int(tokens[0])
