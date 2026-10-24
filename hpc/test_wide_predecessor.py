"""Exercise the actual shell predecessor guard without allocating a job."""
from pathlib import Path
import subprocess
import unittest


class WidePredecessorTests(unittest.TestCase):
    def run_guard(self, *args):
        source = Path(__file__).with_name('bouchet-assembly-wide.sbatch').read_text()
        guard = source[source.index('PREDECESSOR='):source.index('SOURCE_COMMIT=')]
        return subprocess.run(
            ['bash', '-euc', guard + 'printf "%s\\n" "$PREDECESSOR" "$PREVIOUS"',
             'guard', 'checked-controls', *args], capture_output=True, text=True)

    def test_default_is_latest_saved_checkpoint(self):
        result = self.run_guard()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(),
                         ['30320317', '/tmp/triangle-joint-30320317-6YRBV8'])

    def test_subsequent_ended_job_can_be_selected_explicitly(self):
        result = self.run_guard('30330000', '/tmp/triangle-joint-30330000-safe')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(),
                         ['30330000', '/tmp/triangle-joint-30330000-safe'])

    def test_other_jobs_directory_is_rejected(self):
        self.assertNotEqual(self.run_guard('30330000',
            '/tmp/triangle-joint-30320317-6YRBV8').returncode, 0)

    def test_parent_traversal_is_rejected(self):
        self.assertNotEqual(self.run_guard('30330000',
            '/tmp/triangle-joint-30330000-../elsewhere').returncode, 0)

    def test_non_numeric_job_is_rejected(self):
        self.assertNotEqual(self.run_guard('bad',
            '/tmp/triangle-joint-bad-safe').returncode, 0)


if __name__ == '__main__':
    unittest.main()
