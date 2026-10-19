"""Malformed subdivision rejection; these tests do not certify positivity."""
import json
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'lean/tools'))
from generate_apex_replay import parse

class ApexReplayTests(unittest.TestCase):
    def proposal(self,codes):
        return dict(status='complete proposal',frontier=[],Q='1',preorder=codes)

    def test_incomplete_rejected(self):
        p=self.proposal([2]);p['frontier']=[['0','1']]
        with self.assertRaisesRegex(ValueError,'complete proposal'):
            parse(p)

    def test_truncated_and_trailing_rejected(self):
        for codes,message in (([5,2],'Truncated'),([2,3],'Trailing')):
            with self.subTest(codes=codes),self.assertRaisesRegex(ValueError,message):
                parse(self.proposal(codes))

    def test_false_empty_and_unknown_rejected(self):
        for codes,message in (([4],'False empty'),([8],'Unknown')):
            with self.subTest(codes=codes),self.assertRaisesRegex(ValueError,message):
                parse(self.proposal(codes))

    def test_nonpositive_domain_rejected(self):
        p=self.proposal([2]);p['Q']='0'
        with self.assertRaisesRegex(ValueError,'Nonpositive'):
            parse(p)

    def test_complete_f1_geometry(self):
        p=json.loads((ROOT/'lean/data/apex-f1-subdivision-proposal.json').read_text())
        root,data=parse(p)
        self.assertEqual(root.count,31263)
        self.assertEqual(len(data),31263)
        self.assertEqual({r[2] for r in data},{0,1,2})

if __name__=='__main__':
    unittest.main()
