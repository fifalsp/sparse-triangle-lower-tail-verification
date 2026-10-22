import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import continuation_gate as gate
from resume_assembly import COMMIT, REQUIRED, TARGET


class ContinuationGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sources = {f'SparseLowerTail.Fixture{i}': '0' * 64 for i in range(94031)}
        sources[TARGET] = '0' * 64
        cls.manifest = json.dumps(sources).encode()

    def fixture(self, changed=None, state='FAILED', exit_code='124:0', success=False):
        status = {'target': TARGET, 'total': 94032, 'completed': 94032 if success else 26000,
                  'failed': {}, 'phase': 'build_complete' if success else 'building'}
        entries = {'source-manifest.json': self.manifest,
                   'source-commit.txt': COMMIT.encode(),
                   'assembly-inputs.json': json.dumps(
                       {'missing': [], 'selected': {k: {} for k in REQUIRED}}).encode(),
                   'combined-build/status.json': json.dumps(status).encode(),
                   'exit-code.txt': b'0' if success else b'124'}
        if success:
            entries.update({n: b'passed' for n in
                            ['ASSEMBLY_SUCCESS.txt', 'SUCCESS.txt', 'source-hashes-passed.txt']})
            entries['combined-audit.log'] = (b'Axiom audit passed: 123 project declarations, '
                b'100 theorems; only propext, Classical.choice, Quot.sound allowed.')
        entries.update(changed or {})
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / 'result.tar.gz'
            with tarfile.open(archive, 'w:gz') as stream:
                for name, content in entries.items():
                    member = tarfile.TarInfo('logs/' + name)
                    member.size = len(content)
                    stream.addfile(member, io.BytesIO(content))
            with patch.object(gate, 'MANIFEST_SHA', hashlib.sha256(self.manifest).hexdigest()):
                return gate.decision(archive, state, exit_code)

    def test_clean_timeout_resumes(self):
        self.assertEqual(self.fixture(), 'resume')

    def test_success_skips_duplicate_work(self):
        self.assertEqual(self.fixture(state='COMPLETED', exit_code='0:0', success=True), 'finished')

    def test_healthy_running_job_is_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture(state='RUNNING')

    def test_other_failure_is_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture(exit_code='1:0')

    def test_manifest_drift_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'manifest'):
            self.fixture({'source-manifest.json': b'{}'})

    def test_missing_input_or_module_failure_is_rejected(self):
        for changed in [{'assembly-inputs.json': b'{"missing":[],"selected":{}}'},
                        {'combined-build/status.json': json.dumps(
                            {'target':TARGET,'total':94032,'failed':{'bad':1}}).encode()}]:
            with self.assertRaises(ValueError):
                self.fixture(changed)

    def test_success_requires_actual_audit(self):
        with self.assertRaises(ValueError):
            self.fixture({'combined-audit.log': b'Unapproved axiom'},
                         state='COMPLETED', exit_code='0:0', success=True)

    def test_timeout_with_success_marker_is_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture({'ASSEMBLY_SUCCESS.txt': b'contradictory'})


if __name__ == '__main__':
    unittest.main()
