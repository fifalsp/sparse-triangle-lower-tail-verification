#!/usr/bin/env python3
"""Produce actual checked dyadic Taylor leaves and exact slab coverage.
Python proposes endpoints and a subdivision; Lean proves all numerical claims.
"""
from pathlib import Path
from fractions import Fraction as F
from generate_exp_endpoints import endpoint,rat
Q=F(6743,512)
nodes=[];leaves=[]
def tree(lo,hi):
 n=len(nodes);nodes.append([lo,hi,None])
 # Split x and y into four equal strips; refine only the lowest corner in z.
 ax=next((i for i in [0,1]if hi[i]-lo[i]>Q/8),None)
 if ax is None and lo[:2]==[Q/2,Q/2]: ax=2 if hi[2]-lo[2]>Q/16 else None
 if ax is None: leaves.append(n)
 else:
  mid=(lo[ax]+hi[ax])/2;lh=hi.copy();rl=lo.copy();lh[ax]=rl[ax]=mid
  l=tree(lo,lh);r=tree(rl,hi);nodes[n][2]=(ax,mid,l,r)
 return n
tree([Q/2,Q/2,3*Q/8],[Q,Q,Q/2])
vals=sorted(set(a for n in leaves for a in nodes[n][0]+nodes[n][1]+[(a+b)/2 for a,b in zip(*nodes[n][:2])]))
idx={q:i for i,q in enumerate(vals)}
lines=['''import SparseLowerTail.Section05.CoverS1CachedTaylor
import SparseLowerTail.Section05.CoverTreeReplay

/-! Seventeen actual Taylor leaves cover an entire substantial rectangular slab.
Every exponential bracket, integer margin, and subdivision identity is checked
by Lean's kernel. No numerical proposal status is accepted as evidence. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
''']
for i,q in enumerate(vals):
 qq,n,l,u,L,U=endpoint(q,20,60)
 lines += [f'def s1SlabExp{i} : ExpEndpointCertificate :=\n  ⟨{rat(qq)},{n},{rat(l)},{rat(u)},{rat(L)},{rat(U)}⟩',f'theorem s1SlabExp{i}_valid : s1SlabExp{i}.Valid := by decide +kernel']
for n,(lo,hi,split) in enumerate(nodes):
 lines += [f'def s1SlabBox{n} : LogBox := ⟨!['+','.join(rat(a)for a in lo)+'],!['+','.join(rat(a)for a in hi)+']⟩']
 if split is not None: continue
 mid=[(a+b)/2 for a,b in zip(lo,hi)]
 lines += [f'def s1SlabData{n} : S1TaylorBoxData :=\n  ⟨s1SlabBox{n},!['+','.join('s1SlabExp'+str(idx[a])for a in lo)+'],!['+','.join('s1SlabExp'+str(idx[a])for a in hi)+'],!['+','.join('s1SlabExp'+str(idx[a])for a in mid)+']⟩']
 for tag,arr in [('lower',lo),('upper',hi),('center',mid)]:
  lines += [f'theorem s1SlabData{n}_{tag}_valid : ∀ i, (s1SlabData{n}.{tag}Exp i).Valid := by\n  intro i\n  fin_cases i\n'+''.join(f'  · exact s1SlabExp{idx[a]}_valid\n'for a in arr)]
 lines += [f'theorem s1SlabData{n}_margin : 0 < s1SlabData{n}.cachedDyadicMargin := by decide +kernel']
for n in reversed(range(len(nodes))):
 lo,hi,split=nodes[n]
 lines += [f'theorem s1SlabBox{n}_positive {{q : EdgeTriple}} (hq : q ∈ s1SlabBox{n}.region) :\n    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by']
 if split is None:
  lines += [f'  exact s1SlabData{n}.dyadic_positive s1SlabData{n}_lower_valid s1SlabData{n}_upper_valid\n    s1SlabData{n}_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)\n    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData{n}_margin) hq']
 else:
  ax,mid,l,r=split
  lines += [f'  have hl : s1SlabBox{n}.left {ax} {rat(mid)} = s1SlabBox{l} :=\n    LogBox.eq_of_sameEndpoints (by decide +kernel)',f'  have hr : s1SlabBox{n}.right {ax} {rat(mid)} = s1SlabBox{r} :=\n    LogBox.eq_of_sameEndpoints (by decide +kernel)',f'  rcases s1SlabBox{n}.mem_left_or_right hq {ax} {rat(mid)} with h | h',f'  · exact s1SlabBox{l}_positive (hl ▸ h)',f'  · exact s1SlabBox{r}_positive (hr ▸ h)']
lines += ['''/-- Positivity throughout `[Q/2,Q]² × [3Q/8,Q/2]`, where Q=6743/512.
This also proves its entire intersection with the ordered logarithmic domain. -/
theorem coverS1_taylor_slab_positive {q : EdgeTriple}
    (hq : q ∈ s1SlabBox0.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q :=
  s1SlabBox0_positive hq

end SparseLowerTail.Section05
''']
Path('SparseLowerTail/Section05/CoverS1TaylorSlab.lean').write_text('\n\n'.join(lines))
print(f'{len(leaves)} leaves, {len(vals)} unique exponent endpoints, {len(nodes)} nodes')
