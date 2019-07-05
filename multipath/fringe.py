class Fringe(object):
    def __init__(self):
        self.unsat    = list()
        self.deferred = list()
        self.errored  = list()
        self.deferred_addresses = dict()

    def is_empty(self):
        return len(self.deferred) == 0
    
    def get_deferred_by_address(self, address):
        if address in self.deferred_addresses:
            res = self.deferred_addresses[address]
            del self.deferred_addresses[address]
            return res
        return None

    def get_one_deferred(self):
        assert not self.is_empty()
        state = self.deferred.pop()
        del self.deferred_addresses[state.get_ip()]
        return state

    def add_deferred(self, state):
        self.deferred_addresses[state.get_ip()] = state
        self.deferred.append(state)
    
    def add_errored(self, state):
        self.errored.append(state)
