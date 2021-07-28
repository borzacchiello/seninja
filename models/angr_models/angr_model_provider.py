# A compatibility layer between the angr models and SENinja models


class FakeMemory(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state


class FakeState(object):
    def __init__(self, seninja_state):
        self.seninja_state = seninja_state
        self.fake_mem = FakeMemory(seninja_state)

    @property
    def memory(self):
        pass

    @property
    def mem(self):
        raise NotImplementedError


class AngrModelProvider(object):
    def __init__(self):
        self.angr_modes = dict()

    def get_implemented_models(self):
        return list()

    def get_model(self, name):
        raise NotImplementedError
