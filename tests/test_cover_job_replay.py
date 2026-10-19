"""Reject malformed proposals; search regression checks are not formal proofs."""
from copy import deepcopy
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'lean/tools'))
from cover_job_arithmetic import Arithmetic
from generate_cover_job_replay import parse


class CoverJobTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.a = Arithmetic()

    def proposal(self,tree):
        return dict(status='complete proposal',frontier=[],Q='1',preorder=tree)

    def test_all_36_lean_reference_values(self):
        self.assertEqual(self.a.check_reference(),36)
        self.assertEqual([j['index'] for j in self.a.jobs],list(range(36)))

    def test_stale_export_rejected(self):
        d=json.loads(gzip.decompress((ROOT/'lean/data/cover-job-expression-dag.json.gz').read_bytes()))
        d['source_sha256']['Numerics/PolynomialSimplify.lean']='0'*64
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'bad.gz';p.write_bytes(gzip.compress(json.dumps(d).encode()))
            with self.assertRaisesRegex(ValueError,'Stale expression'):
                Arithmetic(p)

    def test_complete_split_and_ordered_tightening(self):
        root, data = parse(self.proposal([5,2,3]))
        self.assertEqual(root.count,2)
        self.assertEqual(data[0][:2],([F(0)]*3,[F(1,2)]*3))
        self.assertEqual(data[1][:2],([F(1,2),F(0),F(0)],[F(1)]*3))

    def test_truncation_rejected(self):
        with self.assertRaisesRegex(ValueError,'Truncated'):
            parse(self.proposal([5,2]))

    def test_trailing_nodes_rejected(self):
        with self.assertRaisesRegex(ValueError,'Trailing'):
            parse(self.proposal([2,3]))

    def test_false_empty_rejected(self):
        with self.assertRaisesRegex(ValueError,'False empty'):
            parse(self.proposal([4]))

    def test_contact_leaf_codes_rejected(self):
        for code in (0,1,8):
            with self.assertRaisesRegex(ValueError,'Unknown'):
                parse(self.proposal([code]))

    def test_frontier_rejected_despite_success_flag(self):
        p=self.proposal([2]);p['frontier']=[['0','1']]
        with self.assertRaisesRegex(ValueError,'completed'):
            parse(p)

    def test_complete_job00_geometry(self):
        p=json.loads(gzip.decompress((ROOT/'lean/data/cover-job-00-subdivision-proposal.json.gz').read_bytes()))
        root,data=parse(p)
        self.assertEqual(len(data),15963)
        self.assertEqual(root.count,len(data))
        for lo,hi,kind in (data[0],data[-1]):
            self.assertEqual(self.a.evaluate(0,lo,hi)['code'],kind)


if __name__=='__main__':
    unittest.main()
