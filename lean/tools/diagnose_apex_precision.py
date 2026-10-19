#!/usr/bin/env python3
"""Untrusted diagnostic: point interval widths just outside ABB neighborhoods.
A negative interval lower bound is not a negative function value.
"""
import json,re
from pathlib import Path
from fractions import Fraction as F
from propose_apex_local_boxes import expr,evaluate
from generate_family_leaf_example import I,S,ep,expbox
ROOT=Path(__file__).resolve().parents[1]
def main():
 src=(ROOT/'SparseLowerTail/Section05/ApexPrimitiveIntervals.lean').read_text().split('def apexPrimitiveBounds',1)[1].split('theorem',1)[0]
 bs=[(F(a),F(b))for a,b in re.findall(r'⟨([0-9/]+),([0-9/]+)⟩',src)]
 constants=[I(I(a).l,I(b).u)for a,b in bs]
 cells=json.loads((ROOT.parent/'data/cover.json').read_text())['cells']
 solutions=json.loads((ROOT/'data/apex-fan-interval-proposal.json').read_text())['solutions']
 expression=expr();rows=[]
 for fan in range(6):
  cell=cells[f'F{fan+1}']
  theta=[I(*solutions[fan][[0,2,3,4].index(j)])if t is None else I(F(t))for j,t in enumerate(cell['theta'])]
  radius=F(cell['local_radii'][1])
  for factor in [F(2),F(20)]:
   q=[sum(bs[0])/2+factor*radius,sum(bs[1])/2,sum(bs[1])/2]
   box=[I(x)for x in q]+[expbox(ep(x),ep(x))for x in q]+constants[4:]+theta+[I(F(cell['lam']))]
   y=evaluate(expression,box)
   rows.append({'fan':fan+1,'contact':'ABB','radius_factor':str(factor),'q':list(map(str,q)),'lower':y.l,'upper':y.u})
   print(f'F{fan+1}',factor,'radius:',y.l/S,y.u/S)
 (ROOT/'data/apex-exterior-precision-diagnostic.json').write_text(json.dumps({'trust_status':'untrusted diagnostic, not a proof; negative interval lower bounds do not imply a negative function value','scale':S,'samples':rows},indent=2)+'\n')
if __name__=='__main__':main()
