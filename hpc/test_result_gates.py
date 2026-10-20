import io,json,tarfile,tempfile,unittest,importlib.util
from pathlib import Path
from audit_result_archives import inspect
from assemble_replays import REQUIRED,generate
from unittest.mock import patch

ROOT=Path(__file__).resolve().parent
class Gates(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  with tarfile.open(ROOT/'triangle-verification-results-20261019-2140.tar.gz') as b:
   data=b.extractfile('sparse-lean-results-30062475.tar.gz').read()
  with tarfile.open(fileobj=io.BytesIO(data)) as t:
   cls.files={m.name:t.extractfile(m).read() for m in t if m.isfile()}
 def archive(self,change):
  files=dict(self.files);change(files);out=io.BytesIO()
  with tarfile.open(fileobj=out,mode='w:gz') as t:
   for n,data in files.items():
    m=tarfile.TarInfo(n);m.size=len(data);t.addfile(m,io.BytesIO(data))
  return out.getvalue()
 def test_real_success(self):
  r=inspect(self.archive(lambda f:None),'test');self.assertTrue(r['verified']);self.assertEqual(r['key'],'cover:25')
 def test_missing_success(self):
  with self.assertRaises(KeyError):inspect(self.archive(lambda f:f.pop('logs/COVER_JOB_SUCCESS.txt')),'test')
 def test_disallowed_axiom(self):
  with self.assertRaises(AssertionError):inspect(self.archive(lambda f:f.update({'logs/cover-job-audit.log':b'uses sorryAx'})),'test')
 def test_incomplete_build(self):
  def mutate(f):
   s=json.loads(f['logs/cover-build/status.json']);s['completed']-=1;f['logs/cover-build/status.json']=json.dumps(s).encode()
  with self.assertRaises(AssertionError):inspect(self.archive(mutate),'test')
 def test_nonzero_exit(self):
  with self.assertRaises(AssertionError):inspect(self.archive(lambda f:f.update({'logs/exit-code.txt':b'124'})),'test')
 def test_full_inventory_required(self):
  r=json.loads((ROOT/'results-20261019-evening/verified-regions.json').read_text());missing=REQUIRED-set(r['verified_regions']);self.assertEqual(len(missing),17);self.assertIn('abb',missing);self.assertIn('exterior',missing)
 def test_assembly_schedules_current_author_proofs(self):
  # A future author module imported only by the root must join the generated
  # certificate assembly's real bounded-build dependency plan.
  spec=importlib.util.spec_from_file_location('bounded_build',ROOT.parent/'lean/tools/build_bounded.py')
  builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
  source=generate({f'cover:{i}':{'kind':'cover'} for i in range(36)})
  with tempfile.TemporaryDirectory() as directory:
   project=Path(directory)
   for line in source.splitlines():
    if line.startswith('import '):
     module=line.removeprefix('import ')
     path=project/Path(module.replace('.','/')).with_suffix('.lean')
     path.parent.mkdir(parents=True,exist_ok=True);path.write_text('')
   future=project/'SparseLowerTail/Section03/FutureAuthorProof.lean'
   future.parent.mkdir(parents=True,exist_ok=True);future.write_text('')
   (project/'SparseLowerTail.lean').write_text('import SparseLowerTail.Section03.FutureAuthorProof\n')
   (project/'SparseLowerTail/CompletedReplays.lean').write_text(source)
   with patch.object(builder,'ROOT',project):graph=builder.dependency_graph('SparseLowerTail.CompletedReplays')
   self.assertIn('SparseLowerTail.Section03.FutureAuthorProof',graph)
   self.assertIn('SparseLowerTail',graph['SparseLowerTail.CompletedReplays'])
if __name__=='__main__':unittest.main()
