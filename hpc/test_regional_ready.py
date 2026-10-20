"""The new Yale wrapper must not accept source drift or an audit failure."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import run_regional_ready as runner


class RegionalGates(unittest.TestCase):
    def run_fixture(self, failure=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            lean = root/'lean'
            (lean/'tools').mkdir(parents=True)
            (lean/'SparseLowerTail').mkdir()
            (lean/'tools/build_bounded.py').write_text("def dependency_graph(target): return {'SparseLowerTail.Fixture': set()}\n")
            proof = lean/'SparseLowerTail/Fixture.lean'
            proof.write_text('theorem fixture : True := True.intro\n')
            audit = lean/'Audit.lean'
            audit.write_text('import SparseLowerTail\n-- unchanged namespace audit fixture\n')
            profile = lean/'lakefile.yale.toml'
            profile.write_text('')
            logs = root/'logs'
            audit_hash = hashlib.sha256(audit.read_bytes()).hexdigest()
            def execute(command, **kwargs):
                if 'build_ready_batches.py' in ' '.join(command):
                    if failure == 'source': proof.write_text('changed proof source\n')
                    if failure == 'policy': audit.write_text('changed audit policy\n')
                if command[0] == 'lake' and failure == 'audit':
                    raise subprocess.CalledProcessError(1, command)
            argv = ['run_regional_ready.py','f1','--logs',str(logs),'--lakefile',str(profile),'--audit-sha256',audit_hash]
            with patch.object(runner,'ROOT',root),patch.object(runner,'LEAN',lean),patch.object(sys,'argv',argv),patch.object(runner.subprocess,'run',side_effect=execute):
                if failure:
                    with self.assertRaises((ValueError,subprocess.CalledProcessError)):runner.main()
                    self.assertFalse((logs/'APEX_SUCCESS.txt').exists())
                    self.assertNotEqual(json.loads((logs/'apex-status.json').read_text())['phase'],'complete')
                else:
                    runner.main()
                    self.assertTrue((logs/'APEX_SUCCESS.txt').is_file())
                    self.assertTrue((logs/'source-hashes-passed.txt').is_file())
    def test_success(self): self.run_fixture()
    def test_changed_source_rejected(self): self.run_fixture('source')
    def test_changed_audit_policy_rejected(self): self.run_fixture('policy')
    def test_failed_axiom_audit_rejected(self): self.run_fixture('audit')


if __name__ == '__main__':unittest.main()
