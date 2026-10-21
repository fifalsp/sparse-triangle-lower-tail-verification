import unittest
import os
import signal
import sys
import tempfile
from unittest.mock import patch
import checkpoint_abb_scaleup as checkpoint
from pathlib import Path
from checkpoint_abb_scaleup import matching_scheduler, active_descendants

class CheckpointSelection(unittest.TestCase):
    def test_only_exact_old_abb_coordinator(self):
        work=Path('/tmp/triangle-yale-30082913-IMipe7')
        command=['python3',str(work/'repo/hpc/build_ready_batches.py'),'--logs',str(work/'logs/family-build')]
        self.assertTrue(matching_scheduler(command,work))
        for other in (Path('/tmp/triangle-yale-30082914-Ke4JN9'),Path('/tmp/triangle-yale-30082913-other')):
            self.assertFalse(matching_scheduler(command,other))
        self.assertFalse(matching_scheduler(['python3','unrelated.py',*command[2:]],work))
        self.assertFalse(matching_scheduler(command[:-1]+[str(work/'logs/exterior-build')],work))

    def test_failure_resumes_selected_scheduler(self):
        with tempfile.TemporaryDirectory() as directory:
            work=Path(directory).resolve()/'triangle-yale-123-fixture'
            handoff=Path(directory)/'handoff'
            handoff.mkdir()
            (handoff/'replacement-ready.txt').write_text('ready')
            argv=['python3',str(work/'repo/hpc/build_ready_batches.py'),
                  '--logs',str(work/'logs/family-build')]
            table={91:dict(ppid=0,state='T',argv=argv)}
            calls=[]
            with patch.dict(os.environ,SLURM_JOB_ID='123'),patch.object(sys,'argv',
                    ['checkpoint','--work',str(work),'--handoff',str(handoff),'--job','123']), \
                 patch.object(checkpoint.signal,'signal'), \
                 patch.object(checkpoint,'process_table',return_value=table), \
                 patch.object(checkpoint.os,'kill',side_effect=lambda *a:calls.append(a)):
                with self.assertRaises(FileNotFoundError): checkpoint.main()
            self.assertEqual(calls,[(91,signal.SIGSTOP),(91,signal.SIGCONT)])

    def test_drain_includes_grandchildren_but_ignores_reaped_work(self):
        table={1:dict(ppid=0,state='T'),2:dict(ppid=1,state='S'),
               3:dict(ppid=2,state='R'),4:dict(ppid=1,state='Z'),
               9:dict(ppid=0,state='R')}
        self.assertEqual(set(active_descendants(table,1)),{2,3})
        table[2]['state']='Z';table[3]['state']='Z'
        self.assertEqual(active_descendants(table,1),[])

if __name__=='__main__':unittest.main()
