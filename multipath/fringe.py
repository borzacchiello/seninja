class Fringe(object):
    def __init__(self):
        self.unsat     = list()
        self.errored   = list()
        self._deferred = dict()

    @property
    def deferred(self):
        res = list()
        for addr in self._deferred:
            res.extend(self._deferred[addr])
        return res

    def is_empty(self):
        return len(self._deferred) == 0
    
    def get_deferred_by_address(self, address):
        if address in self._deferred:
            res = self._deferred[address].pop()
            if len(self._deferred[address]) == 0:
                del self._deferred[address]
            return res
        return None

    def get_one_deferred(self):
        assert not self.is_empty()
        addr, state = self._deferred.popitem()
        return state

    def add_deferred(self, state):
        if state.get_ip() not in self._deferred:
            self._deferred[state.get_ip()] = [state]
        else:
            self._deferred[state.get_ip()].append(state)
    
    def add_errored(self, state):
        self.errored.append(state)
    
    def add_unsat(self, state):
        self.unsat.append(state)
