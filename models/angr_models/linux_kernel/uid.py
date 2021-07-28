from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

class getuid(FakeSimProcedure):
    def run(self):
        return self.state.posix.uid

class getgid(FakeSimProcedure):
    def run(self):
        return self.state.posix.gid

class getresgid(FakeSimProcedure):
    def run(self, rgid_addr, egid_addr, sgid_addr):
        gid = self.state.posix.gid
        self.state.memory.store(rgid_addr, gid)
        self.state.memory.store(egid_addr, gid)
        self.state.memory.store(sgid_addr, gid)
        return 0

class getresuid(FakeSimProcedure):
    def run(self, ruid_addr, euid_addr, suid_addr):
        uid = self.state.posix.uid
        self.state.memory.store(ruid_addr, uid)
        self.state.memory.store(euid_addr, uid)
        self.state.memory.store(suid_addr, uid)
        return 0
