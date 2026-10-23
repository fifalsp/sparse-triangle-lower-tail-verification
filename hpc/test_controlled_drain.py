import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import drain_joint as drain


class ControlledDrainTests(unittest.TestCase):
    def fixture(self, change=None):
        manifest=b'fixture source manifest'
        proof=b'Build completed successfully (3 jobs).\n'
        record=dict(job=drain.JOB,phase='active-proofs-drained',
            authorization='user-approved-six-to-sixteen-worker-handoff',
            manifest_sha256=hashlib.sha256(manifest).hexdigest(),
            audit_sha256=drain.AUDIT_SHA,controller_sha256=drain.CONTROLLER_SHA,
            proof_processes_signalled=[],active_proofs=[dict(module='SparseLowerTail.Leaf',
            completed_log_sha256=hashlib.sha256(proof).hexdigest())])
        data={drain.READY:json.dumps(record).encode(),'source-manifest.json':manifest,
            'combined-build.log':b'Traceback\nKeyboardInterrupt\n',
            'combined-build/SparseLowerTail.Leaf.log':proof}
        if change:change(record,data)
        data[drain.READY]=json.dumps(record).encode()
        with patch.object(drain,'MANIFEST_SHA',hashlib.sha256(manifest).hexdigest()):
            return drain.validate_handoff(data.__getitem__)

    def test_verified_authorized_drained_proof(self):
        self.assertEqual(self.fixture()['phase'],'active-proofs-drained')

    def test_in_progress_or_unapproved_handoff_rejected(self):
        for field,value in [('phase','draining'),('authorization','none'),
                            ('proof_processes_signalled',[123]),('audit_sha256','changed')]:
            with self.assertRaises(ValueError):
                self.fixture(lambda r,d:r.update({field:value}))

    def test_failed_or_modified_active_proof_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture(lambda r,d:d.update({'combined-build/SparseLowerTail.Leaf.log':b'error'}))

    def test_wrong_controller_exit_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture(lambda r,d:d.update({'combined-build.log':b'Lean build failed'}))

    def test_unsafe_or_duplicate_proof_names_rejected(self):
        for mode in ('unsafe','duplicate'):
            def change(record,data):
                if mode=='unsafe':record['active_proofs'][0]['module']='../outside'
                else:record['active_proofs'] *= 2
            with self.assertRaises(ValueError):self.fixture(change)

    def test_interrupt_drains_existing_subprocesses_without_starting_pending_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            script=root/'probe.py'
            script.write_text('''import pathlib,subprocess,sys
from build_ready_batches import build_graph
r=pathlib.Path(sys.argv[1])
def build(name):
 (r/(name+'.started')).write_text('yes')
 subprocess.run([sys.executable,'-c',"import time,pathlib;time.sleep(1);pathlib.Path("+repr(str(r/(name+'.done')))+").write_text('success')"],check=True)
 return 0
build_graph({f'leaf{i}':set() for i in range(12)},set(),lambda b:0,build,6,lambda *a:None)
''')
            env=dict(os.environ,PYTHONPATH=str(Path(__file__).parent))
            with (root/'stderr').open('w') as err:
                process=subprocess.Popen([sys.executable,str(script),str(root)],env=env,stderr=err)
                try:
                    deadline=time.monotonic()+5
                    while len(list(root.glob('*.started')))<6 and time.monotonic()<deadline:
                        time.sleep(.02)
                    self.assertEqual(len(list(root.glob('*.started'))),6)
                    process.send_signal(signal.SIGSTOP)
                    process.send_signal(signal.SIGINT)
                    process.send_signal(signal.SIGCONT)
                    self.assertNotEqual(process.wait(timeout=5),0)
                    self.assertEqual(len(list(root.glob('*.done'))),6)
                    self.assertEqual(len(list(root.glob('*.started'))),6)
                finally:
                    if process.poll() is None:
                        process.send_signal(signal.SIGCONT)
                        process.terminate()
                        process.wait(timeout=5)


if __name__=='__main__':unittest.main()
