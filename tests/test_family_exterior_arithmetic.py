"""Search arithmetic must reproduce values already checked by Lean.

These tests do not replace Lean leaf or coverage proofs.
"""
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'lean/tools'))
from family_exterior_arithmetic import Arithmetic, Program, I, S


class FamilyExteriorArithmeticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.a=Arithmetic()

    def test_matches_checked_smoke_margins(self):
        r=self.a.evaluate([F(39,10)]+[F(99,100)]*3,[F(2503,640)]+[F(101,100)]*3)
        self.assertEqual(r['kind'],'taylor')
        for key in ['value_lower','gradient_upper','gradient_lower']:
            v=self.a.reference[key]
            expected=[F(*x) for x in v] if key.startswith('gradient') else F(*v)
            self.assertEqual(r[key],expected,key)
        self.assertEqual(r['baseline_margin'],F(*self.a.reference['margin']))
        self.assertGreaterEqual(r['margin'],r['baseline_margin'])
        self.assertEqual(r['choices'],[2,2,2])

    def test_matches_all_28_checked_whole_derivatives(self):
        source=(ROOT/'lean/SparseLowerTail/Section08/FamilyParameterSmoke.lean').read_text()
        section=source.split('def intervals :',1)[1].split('theorem intervals_checked',1)[0]
        expected=[tuple(map(int,p)) for p in re.findall(r'⟨(-?\d+),(-?\d+)⟩',section)]
        self.assertEqual(len(expected),28)
        _,ds=self.a.parameters(F(39,10),F(2503,640))
        self.assertEqual([(x.l,x.u) for row in ds for x in row],expected)

    def test_matches_all_21_checked_center_derivatives(self):
        source=(ROOT/'lean/SparseLowerTail/Section08/FamilyExteriorSmoke.lean').read_text()
        section=source.split('def centerD :',1)[1].split('theorem centerD_checked',1)[0]
        expected=[tuple(map(int,p)) for p in re.findall(r'⟨(-?\d+),(-?\d+)⟩',section)]
        self.assertEqual(len(expected),21)
        _,ds=self.a.parameters(F(4999,1280),F(4999,1280))
        self.assertEqual([(x.l,x.u) for row in ds[:3] for x in row],expected)

    def test_reciprocal_crossing_zero_rejected(self):
        p=Program([['v',0],['/',0]],[1])
        with self.assertRaisesRegex(ValueError,'zero'):
            p([I(-S,S)])

    def test_stale_expression_export_rejected(self):
        data=json.loads(gzip.decompress((ROOT/'lean/data/family-expression-dag.json.gz').read_bytes()))
        data['source_sha256']['Numerics/RationalExpr.lean']='0'*64
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'stale.json.gz'
            path.write_bytes(gzip.compress(json.dumps(data).encode()))
            with self.assertRaisesRegex(ValueError,'Stale expression export'):
                Arithmetic(path)


if __name__=='__main__':
    unittest.main()
