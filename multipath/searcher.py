import traceback

class Searcher(object):
    def __init__(self, executor):
        self.target = None
        self.avoid = []
        self.executor = executor

    def __str__(self):
        return "<%s target: %s, %d avoid>" % \
            (
                self.__class__.__name__,
                hex(self.target) if self.target is not None else "None",
                len(self.avoid)
            )

    def __repr__(self):
        return self.__str__()

    def set_target(self, target: int):
        self.target = target

    def add_avoid(self, avoid: int):
        self.avoid.append(avoid)

    def ready_to_run(self):
        return self.target is not None

    def run(self, step_callback=None):
        raise NotImplementedError

class DFSSearcher(Searcher):
    def __init__(self, executor):
        Searcher.__init__(self, executor)

    # override
    def run(self, step_callback=None, findall=False):
        res = []
        while 1:
            if not self.executor.state:
                break
            ip = self.executor.state.get_ip()
            if ip in self.avoid:
                if self.executor.fringe.is_empty():
                    break
                old_state = self.executor.state
                self.executor.fringe.add_avoided(old_state)
                self.executor.state = None
                new_state = self.executor.fringe.get_one_deferred()
                self.executor.set_current_state(new_state)
            ip = self.executor.state.get_ip()
            if ip == self.target:
                res.append(self.executor.state)
                if not findall or self.executor.fringe.is_empty():
                    break
                self.executor.state = None
                new_state = self.executor.fringe.get_one_deferred()
                self.executor.set_current_state(new_state)

            try:
                self.executor.execute_one()
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break

            if step_callback is not None:
                if not step_callback(self.executor.state):
                    break

        if not findall:
            return res[0] if len(res) > 0 else None

        state_res = res[0]
        self.executor.set_current_state(state_res)
        for state in res[1:]:
            self.executor.fringe.add_deferred(state)
        return state_res

class BFSSearcher(Searcher):
    def __init__(self, executor):
        Searcher.__init__(self, executor)

    def _continue_until_branch(self, step_callback):
        k = self.executor.fringe.last_added
        i = k
        while i == k:
            if not self.executor.state:
                return None
            ip = self.executor.state.get_ip()
            if ip in self.avoid:
                if self.executor.fringe.is_empty():
                    return None
                old_state = self.executor.state
                self.executor.fringe.add_avoided(old_state)
                self.executor.state = None
                new_state = self.executor.fringe.get_one_deferred()
                self.executor.set_current_state(new_state)
            ip = self.executor.state.get_ip()
            if ip == self.target:
                return True

            try:
                self.executor.execute_one()
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                return None

            if step_callback is not None:
                if not step_callback(self.executor.state):
                    return None

            i = self.executor.fringe.last_added

        return False

    # override
    def run(self, step_callback=None):
        while 1:
            res = self._continue_until_branch(step_callback)
            if res is None:
                return None
            if res:
                return self.executor.state

            new_state = self.executor.fringe.get_random_deferred()
            self.executor.set_current_state(new_state)
