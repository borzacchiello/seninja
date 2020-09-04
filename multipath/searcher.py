import traceback


class Searcher(object):
    def __init__(self, executor):
        self.target = None
        self.avoid = []
        self.executor = executor

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
    def run(self, step_callback=None):
        res = None
        while 1:
            try:
                self.executor.execute_one()
            except Exception as e:
                print("!ERROR!:")
                print(traceback.format_exc())
                break
            if not self.executor.state:
                break
            ip = self.executor.state.get_ip()
            if ip == self.target:
                res = self.executor.state
                break
            elif ip in self.avoid:
                if self.executor.fringe.is_empty():
                    break
                old_state = self.executor.state
                self.executor.fringe.add_avoided(old_state)
                self.executor.state = None
                new_state = self.executor.fringe.get_one_deferred()
                self.executor.set_current_state(new_state)

            if step_callback is not None:
                if not step_callback(self.executor.state):
                    break

        return res
