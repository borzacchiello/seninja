from .. import FakeSimProcedure, FakeSimProcedureError, claripy, SIM_PROCEDURES

######################################
# stub, for unsupported syscalls
######################################

#pylint:disable=redefined-builtin,arguments-differ
class syscall(FakeSimProcedure):

    def run(self, resolves=None):

        self.resolves = resolves  # pylint:disable=attribute-defined-outside-init

        if self.successors is not None:
            self.successors.artifacts['resolves'] = resolves

        return self.state.solver.Unconstrained("syscall_stub_%s" % self.display_name, self.state.arch.bits, key=('syscall', '?', self.display_name))

    def __repr__(self):
        if 'resolves' in self.kwargs:
            return '<Syscall stub (%s)>' % self.kwargs['resolves']
        else:
            return '<Syscall stub>'
