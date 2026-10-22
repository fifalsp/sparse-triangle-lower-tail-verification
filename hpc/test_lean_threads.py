import unittest
from set_lean_threads import revised_profile

BASE = 'name="test"\nweakLeanArgs = ["-M49152", "-j1", "-s65536"]\ndefaultTargets=["Test"]\n'


class LeanThreadTests(unittest.TestCase):
    def test_only_thread_count_changes(self):
        self.assertEqual(revised_profile(BASE, 1, 2, 6, 12), BASE.replace('"-j1"', '"-j2"'))

    def test_cannot_exceed_allocated_cpus(self):
        with self.assertRaisesRegex(ValueError, 'allocation'):
            revised_profile(BASE, 1, 3, 6, 12)

    def test_rejects_unexpected_bounds_or_previous_setting(self):
        for before in [BASE.replace('-M49152', '-M0'),
                       BASE.replace('-s65536', '-s8192'), BASE.replace('-j1', '-j4')]:
            with self.assertRaises(ValueError):
                revised_profile(before, 1, 2, 6, 12)

    def test_reversible_without_other_changes(self):
        changed = revised_profile(BASE, 1, 2, 6, 12)
        self.assertEqual(revised_profile(changed, 2, 1, 6, 12), BASE)


if __name__ == '__main__':
    unittest.main()
