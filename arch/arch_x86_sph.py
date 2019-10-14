from arch.arch_abstract import SpecialInstructionHandler
import z3

class ArchX86SPH(SpecialInstructionHandler):
    def handle_instruction(self, disasm_str: str, state):

        inst_name  = disasm_str.split(" ")[0]
        parameters = ''.join(disasm_str.split(" ")[1:]).split(",")

        handle_name = "{}_handler".format(inst_name)
        if hasattr(self, handle_name):
            getattr(handle_name, self)(state, parameters)
            return True
        return False
    
    def handle_cmov(self, state, parameters):
        pass
