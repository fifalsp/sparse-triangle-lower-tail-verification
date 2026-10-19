#!/usr/bin/env python3
"""Generate kernel-checked subdivision coverage, independently of leaf margins.
Every exact split/tightening and table lookup is replayed by Lean. This script
is untrusted. Its output never makes a positivity assertion without hypotheses.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse,json
from generate_exp_endpoints import rat
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'SparseLowerTail/Section05/S1Replay'
@dataclass
class Node:
 lo:list
 hi:list
 code:int
 children:tuple=()
 leaf:int=-1
 count:int=0
 chunk:int=-1

def parse():
 p=json.loads((ROOT/'data/s1-horner-subdivision-proposal.json').read_text())
 it=iter(p['preorder']); index=0
 def go(lo,hi):
  nonlocal index
  lo=[max(lo),max(lo[1:]),lo[2]];hi=[hi[0],min(hi[:2]),min(hi)]
  code=next(it);n=Node(lo,hi,code)
  if code>=5:
   ax=code-5;mid=(lo[ax]+hi[ax])/2;lh=hi.copy();rl=lo.copy();lh[ax]=rl[ax]=mid
   n.children=(go(lo,lh),go(rl,hi));n.count=sum(c.count for c in n.children)
  elif code==2:n.leaf=index;index+=1;n.count=1
  elif code!=4:raise ValueError(code)
  return n
 root=go([F(0)]*3,[F(p['Q'])]*3)
 if next(it,None) is not None:raise ValueError('Trailing tree nodes')
 return root

def box(n):return '⟨!['+','.join(map(rat,n.lo))+'],!['+','.join(map(rat,n.hi))+']⟩'
def leaves(n):
 if n.code==2:return [n.leaf]
 return sum((leaves(c)for c in n.children),[])
def table(xs):
 if len(xs)==1:return f'(.leaf ({xs[0]}))'
 return f'(.branch {table(xs[::2])} {table(xs[1::2])})'
def padded(xs):return xs+['none']*((1<<(len(xs)-1).bit_length())-len(xs))
def tree(n,mapping,stop=False):
 if stop and n.chunk>=0:return f'(.leaf {n.chunk})'
 if n.code==2:return f'(.leaf {mapping[n.leaf]})'
 if n.code==4:return '.empty'
 return f'(.split {n.code-5} {tree(n.children[0],mapping,stop)} {tree(n.children[1],mapping,stop)})'
def header(imports):return '\n'.join('import '+i for i in imports)+'''\n\n/-! Exact subdivision coverage only; nonlinear leaf inequalities are supplied separately. -/
namespace SparseLowerTail.Section05.S1Replay
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
def generate(limit=64,only=None):
 root=parse();chunks=[]
 def cut(n):
  if n.count<=limit:n.chunk=len(chunks);chunks.append(n)
  else:
   for c in n.children:cut(c)
 cut(root)
 for k,n in enumerate(chunks):
  if only is not None and k!=only:continue
  ids=leaves(n);name=f'Coverage{k:03d}';ns=f'Coverage{k:03d}'
  imports=['SparseLowerTail.Section05.CoverReplayTable']+[f'SparseLowerTail.Section05.S1Replay.Boxes{b:03d}'for b in sorted({i//256 for i in ids})]
  txt=header(imports)+f'\nnamespace {ns}\ndef initialBox : LogBox := {box(n)}\n'
  txt+=f'def leafTable : RegisterTree (Option LogBox) :=\n  {table(padded([f"some box{i}"for i in ids]))}\n'
  txt+=f'def subdivision : CoverReplayTree :=\n  {tree(n,{i:j for j,i in enumerate(ids)})}\n'
  txt+='theorem subdivision_valid : subdivision.Valid leafTable.get initialBox := by decide +kernel\n'
  txt+='''theorem covered {Q : ℝ} {P : EdgeTriple → Prop}
    (h : leafTable.All (CoverBoxProperty Q P)) :
    ∀ q∈initialBox.region,q∈orderedLogDomain Q → P q :=
  subdivision.sound_table h subdivision_valid
'''
  txt+=f'end {ns}\nend SparseLowerTail.Section05.S1Replay\n'
  (OUT/(name+'.lean')).write_text(txt)
 if only is None:
  txt=header([f'SparseLowerTail.Section05.S1Replay.Coverage{k:03d}'for k in range(len(chunks))])
  txt+='\nnamespace Coverage\n'+f'def initialBox : LogBox := {box(root)}\n'
  txt+=f'def chunkTable : RegisterTree (Option LogBox) :=\n  {table(padded([f"some Coverage{k:03d}.initialBox"for k in range(len(chunks))]))}\n'
  txt+=f'def subdivision : CoverReplayTree :=\n  {tree(root,{},True)}\n'
  txt+='theorem subdivision_valid : subdivision.Valid chunkTable.get initialBox := by decide +kernel\n'
  txt+='''theorem covered {Q : ℝ} {P : EdgeTriple → Prop}
    (h : chunkTable.All (CoverBoxProperty Q P)) :
    ∀ q∈initialBox.region,q∈orderedLogDomain Q → P q :=
  subdivision.sound_table h subdivision_valid
end Coverage
end SparseLowerTail.Section05.S1Replay
'''
  (OUT/'Coverage.lean').write_text(txt)
 (ROOT/'data/s1-coverage-index.json').write_text(json.dumps({'chunk_leaf_limit':limit,'chunks':[{'chunk':k,'leaves':leaves(n)}for k,n in enumerate(chunks)]},indent=2)+'\n')
 print(f'{len(chunks)} subtrees; {root.count} leaves; only={only}')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--only',type=int);p.add_argument('--limit',type=int,default=64);a=p.parse_args();generate(a.limit,a.only)
