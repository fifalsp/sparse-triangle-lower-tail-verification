import io,json,tarfile,tempfile,unittest
from pathlib import Path
from audit_result_archives import inspect
from assemble_replays import REQUIRED

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
if __name__=='__main__':unittest.main()
