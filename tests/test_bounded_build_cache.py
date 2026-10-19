"""Cache existence never suffices: require Lake success and dependency closure."""
from pathlib import Path
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'lean/tools'))
from build_bounded import verified_cached_modules

class CacheTests(unittest.TestCase):
    def run_case(self,graph,files,check,batch_size=128):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder)
            for module in files:
                p=root/'.lake/build/lib/lean'/Path(module.replace('.','/')).with_suffix('.olean')
                p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'untrusted fixture')
            return verified_cached_modules(graph,root,check,batch_size)

    def test_artifact_absence_is_not_cached(self):
        def forbidden(_):self.fail('No candidates should be passed to Lake')
        self.assertEqual(self.run_case({'A':set()},[],forbidden),set())

    def test_artifact_presence_without_validation_is_rejected(self):
        self.assertEqual(self.run_case({'A':set()},['A'],lambda _:False),set())

    def test_validated_dependency_closed_batch_is_reused(self):
        self.assertEqual(self.run_case({'A':{'B'},'B':set()},['A','B'],lambda _:True),{'A','B'})

    def test_failed_dependency_prunes_an_accepted_dependent(self):
        self.assertEqual(self.run_case({'A':{'B'},'B':set()},['A','B'],lambda b:b==['A'],1),set())

    def test_missing_transitive_dependency_preserves_only_independent_modules(self):
        graph={'A':{'B'},'B':{'C'},'C':set(),'D':set()}
        self.assertEqual(self.run_case(graph,['A','B','D'],lambda _:True),{'D'})

    def test_failed_batch_is_not_partially_accepted(self):
        graph={str(i):set() for i in range(5)};calls=[]
        def check(batch):
            calls.append(batch)
            return batch==['4']
        self.assertEqual(self.run_case(graph,graph,check,2),{'4'})
        self.assertEqual([len(b) for b in calls],[2,2,1])

if __name__=='__main__':unittest.main()
