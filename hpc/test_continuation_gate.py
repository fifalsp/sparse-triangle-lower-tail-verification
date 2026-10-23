import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import continuation_gate as gate
import drain_joint as drain
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

    def test_authorized_drain_resumes_only_with_finished_active_proofs(self):
        proof=b'Build completed successfully (3 jobs).'
        manifest_sha=hashlib.sha256(self.manifest).hexdigest()
        record=dict(job=drain.JOB,phase='active-proofs-drained',
                    authorization='user-approved-six-to-sixteen-worker-handoff',
                    manifest_sha256=manifest_sha,audit_sha256=drain.AUDIT_SHA,
                    controller_sha256=drain.CONTROLLER_SHA,proof_processes_signalled=[],
                    active_proofs=[dict(module='SparseLowerTail.Leaf',
                        completed_log_sha256=hashlib.sha256(proof).hexdigest())])
        changed={'exit-code.txt':b'1',drain.READY:json.dumps(record).encode(),
                 'combined-build.log':b'KeyboardInterrupt',
                 'combined-build/SparseLowerTail.Leaf.log':proof}
        with patch.object(drain,'MANIFEST_SHA',manifest_sha):
            self.assertEqual(self.fixture(changed,exit_code='1:0'),'resume')
            changed['combined-build/SparseLowerTail.Leaf.log']=b'error'
            with self.assertRaises(ValueError):self.fixture(changed,exit_code='1:0')

    def test_exit_one_without_drain_evidence_is_rejected(self):
        with self.assertRaises(ValueError):self.fixture({'exit-code.txt':b'1'},exit_code='1:0')

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
