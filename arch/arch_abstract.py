class Arch(object):  # abstract class
    def bits(self):
        raise NotImplementedError
    def regs_data(self):
        raise NotImplementedError
    def flags_data(self):
        raise NotImplementedError
    def endness(self):
        raise NotImplementedError
    def getip_reg(self):
        raise NotImplementedError
    def get_base_pointer_reg(self):
        raise NotImplementedError
    def get_stack_pointer_reg(self):
        raise NotImplementedError
