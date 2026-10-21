"""Scheduling gates for the Delta cache-resumption path (no Lean processes)."""
import unittest
from threading import Event, Lock
from build_ready_batches import build_graph


class ReadyBatchTests(unittest.TestCase):
    def test_failed_cache_falls_back_before_dependent_check(self):
        graph = {'base': set(), 'leaf': {'base'}, 'root': {'leaf'}}
        events = []
        def check(batch):
            events.append(('check', batch))
            return 3 if batch == ['base'] else 0
        def build(name):
            events.append(('build', name))
            return 0
        self.assertEqual(build_graph(graph, set(graph), check, build, 2, lambda *a: None), set(graph))
        self.assertEqual(events, [('check', ['base']), ('build', 'base'),
                                  ('check', ['leaf']), ('check', ['root'])])

    def test_failed_dependency_blocks_dependents(self):
        graph = {'base': set(), 'root': {'base'}}
        built = []
        with self.assertRaises(RuntimeError):
            build_graph(graph, set(graph), lambda batch: 3,
                        lambda name: built.append(name) or 1, 2, lambda *a: None)
        self.assertEqual(built, ['base'])

    def test_no_artifact_is_never_cache_checked(self):
        events = []
        def check(batch):
            self.fail('Missing artifact must use normal build')
        self.assertEqual(build_graph({'root': set()}, set(), check,
                                    lambda name: events.append(name) or 0, 1, lambda *a: None), {'root'})
        self.assertEqual(events, ['root'])

    def test_cycle_or_missing_dependency_rejected(self):
        for graph in ({'a': {'b'}, 'b': {'a'}}, {'a': {'absent'}}):
            with self.assertRaises(ValueError):
                build_graph(graph, set(), lambda batch: 0, lambda name: 0, 1, lambda *a: None)

    def test_freed_worker_refilled_before_slow_sibling(self):
        third_started = Event()
        lock = Lock()
        running = 0
        peak = 0
        def build(name):
            nonlocal running, peak
            with lock:
                running += 1
                peak = max(peak, running)
            try:
                if name == 'a':
                    if not third_started.wait(2):
                        raise AssertionError('Freed worker was left idle')
                elif name == 'c':
                    third_started.set()
                return 0
            finally:
                with lock: running -= 1
        graph = {name: set() for name in 'abcd'}
        self.assertEqual(build_graph(graph, set(), lambda batch: 0, build, 2,
                                    lambda *args: None), set(graph))
        self.assertEqual(peak, 2)

    def test_failure_stops_new_submissions(self):
        submitted = []
        def build(name):
            submitted.append(name)
            return 1
        with self.assertRaises(RuntimeError):
            build_graph({name: set() for name in 'abc'}, set(), lambda batch: 0,
                        build, 1, lambda *args: None)
        self.assertEqual(submitted, ['a'])

    def test_cache_batches_bounded_and_complete(self):
        graph = {str(i): set() for i in range(300)}
        batches = []
        def check(batch):
            batches.append(batch)
            return 0
        self.assertEqual(build_graph(graph, set(graph), check, lambda name: self.fail(name),
                                    3, lambda *a: None), set(graph))
        self.assertEqual([len(b) for b in batches], [128, 128, 44])
        self.assertEqual({m for batch in batches for m in batch}, set(graph))


if __name__ == '__main__':
    unittest.main()
