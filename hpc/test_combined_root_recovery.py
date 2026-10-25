import copy
import hashlib
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

import recover_combined_root as recovery


class CombinedRootRecoveryTests(unittest.TestCase):
    def setUp(self):
        sources = {recovery.TARGET: 'root', **{
            'SparseLowerTail.Test' + str(i): 'source' for i in range(recovery.TOTAL - 1)}}
        self.data = {
            'source-manifest.json': json.dumps(sources).encode(),
            'source-commit.txt': recovery.COMMIT.encode(), 'exit-code.txt': b'1\n',
            'combined-build/status.json': json.dumps(dict(target=recovery.TARGET,
                total=recovery.TOTAL, completed=recovery.TOTAL - 1,
                phase='build_failed', failed={recovery.TARGET: -6})).encode(),
            'assembly-inputs.json': json.dumps(dict(missing=[], selected={
                name: {} for name in recovery.REQUIRED})).encode(),
            'root-failure.log': b'Stack overflow detected. Aborting.\n',
            'success-marker': False}
        self.manifest_sha = hashlib.sha256(self.data['source-manifest.json']).hexdigest()

    def validate(self, data, state='FAILED', exit_code='1:0'):
        with patch.object(recovery, 'MANIFEST_SHA', self.manifest_sha):
            return recovery.validate_data(data, state, exit_code)

    def mutate_status(self, **changes):
        data = copy.deepcopy(self.data)
        status = json.loads(data['combined-build/status.json'])
        status.update(changes)
        data['combined-build/status.json'] = json.dumps(status).encode()
        return data

    def test_accepts_only_isolated_root_stack_overflow(self):
        self.assertEqual(len(self.validate(self.data)), recovery.TOTAL)

    def test_rejects_dependency_failure(self):
        with self.assertRaises(ValueError):
            self.validate(self.mutate_status(failed={'SparseLowerTail.Test0': -6}))

    def test_rejects_unfinished_dependencies(self):
        with self.assertRaises(ValueError):
            self.validate(self.mutate_status(completed=recovery.TOTAL - 2))

    def test_rejects_non_abort_exit(self):
        with self.assertRaises(ValueError):
            self.validate(self.mutate_status(failed={recovery.TARGET: 1}))

    def test_requires_literal_stack_overflow_evidence(self):
        data = dict(self.data, **{'root-failure.log': b'type mismatch'})
        with self.assertRaises(ValueError):
            self.validate(data)

    def test_rejects_changed_manifest(self):
        data = dict(self.data, **{'source-manifest.json': b'{}'})
        with self.assertRaises(ValueError):
            self.validate(data)

    def test_rejects_missing_base_input(self):
        data = dict(self.data, **{'assembly-inputs.json': b'{"missing":[],"selected":{}}'})
        with self.assertRaises(ValueError):
            self.validate(data)

    def test_rejects_contradictory_success(self):
        with self.assertRaises(ValueError):
            self.validate(dict(self.data, **{'success-marker': True}))

    def test_rejects_other_scheduler_outcome(self):
        with self.assertRaises(ValueError):
            self.validate(self.data, state='COMPLETED', exit_code='0:0')

    def test_stack_option_applies_to_lake_runtime_itself(self):
        self.assertEqual(recovery.lake_command(Path('/control/frontend.lean'),
            Path('/repo/profile.toml'), 49152, 262144),
            ['lean', '-M49152', '-s262144', '--run', '/control/frontend.lean',
             '--file', '/repo/profile.toml'])

    def test_actual_pinned_frontend_starts(self):
        lean = Path.home() / '.elan/toolchains/leanprover--lean4---v4.24.0/bin/lean'
        if not lean.exists():
            self.skipTest('Pinned local runtime unavailable')
        frontend = Path(recovery.__file__).with_name('lake_stack_frontend.lean')
        result = subprocess.run([str(lean), '-s262144', '--run', str(frontend),
                                 '--version'], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Lean version 4.24.0', result.stdout)


if __name__ == '__main__':
    unittest.main()
