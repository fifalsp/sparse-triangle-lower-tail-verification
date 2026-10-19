"""Coverage-parser regressions; these do not replace Lean coverage proofs."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'lean/tools'))
from generate_family_exterior_replay import parse
from generate_family_abb_replay import ids, replay


def proposal():
    lo=['39/10','0','0','0'];hi=['19/2','12','12','12']
    left=hi.copy();left[1]='6'
    right=lo.copy();right[1]='6'
    return dict(frontier=[],initial=[lo,hi],tree=[1,-1,-2],leaves=[
        dict(kind='taylor',lower=lo,upper=left),
        dict(kind='aaa',lower=right,upper=hi)])


class ExteriorReplayParserTests(unittest.TestCase):
    def test_exact_split_and_leaf_index_order(self):
        root=parse(proposal())
        self.assertEqual(ids(root),[0,1])
        self.assertEqual(replay(root,{0:1,1:0}),'(.split 1 (.leaf 1) (.leaf 0))')
        self.assertEqual(root.count,2)

    def test_rejects_wrong_bounds(self):
        p=proposal();p['leaves'][0]['upper'][1]='5'
        with self.assertRaises(ValueError):parse(p)

    def test_rejects_duplicate_leaf(self):
        p=proposal();p['tree'][-1]=-1
        with self.assertRaises(ValueError):parse(p)

    def test_rejects_uncovered_frontier(self):
        p=proposal();p['frontier']=[p['initial']]
        with self.assertRaises(ValueError):parse(p)

    def test_rejects_extra_leaf_record(self):
        p=proposal();p['leaves'].append(copy.deepcopy(p['leaves'][0]))
        with self.assertRaises(ValueError):parse(p)

    def test_rejects_wrong_scope(self):
        p=proposal();p['initial'][0][0]='4'
        with self.assertRaises(ValueError):parse(p)


if __name__=='__main__':unittest.main()
