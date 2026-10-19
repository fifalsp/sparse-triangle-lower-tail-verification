#!/usr/bin/env python3
"""Generate a finite batch of actual Lean Taylor leaf proofs.
All proposed integer comparisons and interval inputs are checked by the kernel.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import argparse,json
from generate_s1_replay_data import ROOT,OUT,boxes_from_proposal
from generate_exp_endpoints import endpoint
from s1_expr_model import T,O,MU
SCALE=2**60
@lru_cache(None)
def exp(q):return endpoint(q,20,60)[-2:]
def dyad(pair):
 a,b=pair
 return f'⟨{a.numerator*SCALE//a.denominator},{-((-b.numerator*SCALE)//b.denominator)}⟩'
def main():
 parser=argparse.ArgumentParser();parser.add_argument('batch',type=int);parser.add_argument('--size',type=int,default=128);args=parser.parse_args()
 leaves=boxes_from_proposal();start=args.batch*args.size;stop=min(start+args.size,len(leaves))
 if not 0<=start<stop:raise ValueError('No leaves in batch')
 vals=list(map(F,json.loads((ROOT/'data/s1-replay-index.json').read_text())['endpoint_arguments']));idx={q:i for i,q in enumerate(vals)}
 lines=[*(f'import SparseLowerTail.Section05.S1Replay.Boxes{k:03d}'for k in range(start//256,(stop-1)//256+1)),
 'import SparseLowerTail.Section05.S1Replay.Endpoints','import SparseLowerTail.Section05.CoverS1ConstantTaylor','',
 '/-! Actual kernel-checked whole-box inequalities for exact S1 vertex zero. -/',
 f'namespace SparseLowerTail.Section05.S1Replay.Batch{args.batch:03d}',
 'open Numerics','set_option maxRecDepth 100000','set_option maxHeartbeats 4000000','']
 for n in range(start,stop):
  lo,hi=leaves[n];mid=[(a+b)/2 for a,b in zip(lo,hi)];rad=[(b-a)/2 for a,b in zip(lo,hi)]
  lines += [f'def data{n} : S1TaylorBoxData :=\n  ⟨box{n},!['+','.join(f'exp{idx[q]}'for q in lo)+'],!['+','.join(f'exp{idx[q]}'for q in hi)+'],!['+','.join(f'exp{idx[q]}'for q in mid)+']⟩']
  for tag,arr in [('lower',lo),('upper',hi),('center',mid)]:
   lines += [f'theorem data{n}_{tag}_valid : ∀ i,(data{n}.{tag}Exp i).Valid := by\n  intro i\n  fin_cases i\n'+''.join(f'  · exact exp{idx[q]}_valid\n'for q in arr)]
  s=[(q,q)for q in mid]+[exp(q)for q in mid]+[T,O,MU]
  w=list(zip(lo,hi))+[(exp(b)[0],exp(a)[1])for a,b in zip(lo,hi)]+[T,O,MU]
  velocity=[(-r,r)for r in rad]
  for name,arr,target in [('start',s,'Start'),('whole',w,'Whole'),('velocity',velocity,'Velocity')]:
   lines += [f'def {name}{n} : Fin {len(arr)} → DyadicInterval := !['+','.join(map(dyad,arr))+']',f'theorem {name}{n}_eq : ∀ i,{name}{n} i=data{n}.dyadic{target} i := by decide +kernel']
  lines += [f'theorem margin{n} : 0 < s1LiteralMargin start{n} whole{n} velocity{n} := by decide +kernel',
   f'theorem positive{n} {{q : EdgeTriple}} (hq : q ∈ box{n}.region) :\n    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by\n  exact data{n}.literal_positive start{n} whole{n} velocity{n}\n    start{n}_eq whole{n}_eq velocity{n}_eq data{n}_lower_valid data{n}_upper_valid data{n}_center_valid\n    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin{n} hq']
 lines += [f'end SparseLowerTail.Section05.S1Replay.Batch{args.batch:03d}','']
 path=OUT/f'Leaves{args.batch:03d}.lean';path.write_text('\n\n'.join(lines));print(f'{stop-start} leaves -> {path.relative_to(ROOT)}')
if __name__=='__main__':main()
