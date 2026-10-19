#!/usr/bin/env python3
"""Emit checked S1 interval leaves for a larger near-one cube and a tail cube.
The rational leaf bounds are fully checked in Lean; no verifier status is imported.
"""
from pathlib import Path
from fractions import Fraction as F
import json,argparse
import cover_interval_codegen as cg
from cover_interval_codegen import Node,q,emit
ROOT=Path(__file__).resolve().parents[2]
cell=json.loads((ROOT/'data/cover.json').read_text())['cells']['S1']
Q=F(cell['Q']);m,Fv=map(F,cell['vertices'][0])
configs={'Tail':([F(8)]*3,[Q]*3,F(1,100))}
for i in range(8):
 bits=[(i>>j)&1 for j in [2,1,0]]
 configs[f'Near{i}']=([F(b,64) for b in bits],[F(b+1,64) for b in bits],F(1,2))
parser=argparse.ArgumentParser();parser.add_argument('regions',nargs='*',choices=list(configs));args=parser.parse_args()
for tag in args.regions or configs:
 cg.reset();lo,hi,target=configs[tag];prefix='coverS1'+tag
 header='''import SparseLowerTail.Section05.CoverS1FirstBox
import SparseLowerTail.Section05.BoxExponentialBounds

/-! Generated proof-producing S1 subdomain certificate, stable anchor `prop:cover`.
This is one leaf region, not the complete cover. The coefficients and parameter
vertex are the exact S1 data defined in CoverS1FirstBox. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04 Numerics
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
'''
 def rq(v):return q(v).replace('ℝ','ℚ')
 header+=f'def {prefix}Box : LogBox := ⟨!['+','.join(rq(x) for x in lo)+'],!['+','.join(rq(x) for x in hi)+']⟩\n\n'
 xs=[];logs=[]
 for i,(coord,n) in enumerate(zip(['qv.1.1','qv.1.2','qv.2'],['x','y','z'])):
  emit(f'  have h{n}q : {coord} ∈ Set.Icc {q(lo[i])} {q(hi[i])} := by')
  emit(f'    have h := hq {i}')
  emit(f'    simp only [{prefix}Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h')
  emit('    norm_num at h ⊢\n    exact h')
  el,eu=(F(0),F(1,2900)) if tag=='Tail' else (1-hi[i],1/(1+lo[i]))
  emit(f'  have h{n} : Bounds (Real.exp (-{coord})) {q(el)} {q(eu)} := by')
  if tag=='Tail':emit(f'    exact exp_neg_tail_bounds h{n}q.1')
  else:emit(f'    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ {q(lo[i])}) h{n}q using 1 <;> norm_num')
  emit(f'  have hl{n} : Bounds (Real.log (Real.exp (-{coord}))) {q(-hi[i])} {q(-lo[i])} := by')
  emit(f'    convert log_exp_neg_bounds h{n}q using 1 <;> norm_num')
  xs.append(Node(f'(Real.exp (-{coord}))',el,eu,'h'+n))
  logs.append(Node(f'(Real.log (Real.exp (-{coord})))',-hi[i],-lo[i],'hl'+n))
 one=Node.c(1);two=Node.c(2);threeinv=Node.c(F(1,3));zero=Node.c(0)
 T=Node('criticalTriangle',F(9217366866,10**12),F(9217366881,10**12),'criticalTriangle_sharp_bounds')
 O=Node('criticalOmega',F(92312137,10**8),F(92312139,10**8),'criticalOmega_checked_bounds')
 M=Node.c(m);C=Node.c(Fv)
 mu=((one-C)-M)/T;mu=mu.pin('relaxationMultiplier coverS1Vertex0','hmu')
 k=(one+C)-M;k=k.pin('relaxationVertexMean coverS1Vertex0','hk')
 mullogs=[x*l for x,l in zip(xs,logs)]
 entropies=[];vs=[];gs=[]
 for i,(x,ml) in enumerate(zip(xs,mullogs)):
  h=(ml-x)+one;h=h.pin(f'entropy {x.e}',f'he{i}')
  h=h.nonneg('entropy_nonneg (le_of_lt (Real.exp_pos _))');entropies.append(h)
  ve=(ml-two*x)+two;ve=ve.pin(f'vertexEntropy {x.e}',f'hve{i}');vs.append(ve)
  g=x+O*h;g=g.pin(f'criticalObservable {x.e}',f'hg{i}');gs.append(g)
 def avg(ns):return ((ns[0]+ns[1])+ns[2])*threeinv
 features=[avg(xs)-M,xs[0]*xs[1]*xs[2]-T,avg(entropies)-C]
 for j in range(5):
  terms=[]
  for i in range(3):
   et=one if j==0 else xs[i] if j==1 else xs[i].pow(j) if j<4 else mullogs[i]
   terms.append(et*(logs[i]+mu*xs[(i+1)%3]*xs[(i+2)%3]))
  features.append(avg(terms))
 for j in range(4):
  terms=[]
  for i in range(3):
   vt=xs[i] if j==0 else xs[i].pow(j+2) if j<3 else mullogs[i]
   terms.append(vt*((vs[(i+1)%3]+vs[(i+2)%3])-two*k))
  features.append(avg(terms))
 features=[f.pin(f'certificateFeature {i} (logBoxEdges qv) coverS1Vertex0',f'hf{i}') for i,f in enumerate(features)]
 H=avg([g.pow(2) for g in gs])-two*avg([gs[i]*gs[(i+1)%3] for i in range(3)])+(M+O*C).pow(2)
 H=H.pin('certificateHoeffding (logBoxEdges qv) coverS1Vertex0','hH')
 terms=[Node.c(c)*f for c,f in zip(cell['theta'],features)]
 s=zero
 for term in reversed(terms):s=term+s
 cert=s.neg()-Node.c(cell['lam'])*H
 assert cert.l>target,(tag,cert.l,target)
 print(tag,'interval',float(cert.l),float(cert.u))
 emit(f'  have heq : {cert.e} = logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by')
 emit('    dsimp only ['+','.join(f'v{i}' for i in range(1,Node.count+1))+']')
 emit('    rw [logCertificate,coverCertificate_fin12_expansion]')
 emit('    simp only [coverS1Theta,coverS1Lam,Matrix.cons_val]\n    ring')
 emit(f'  rw [heq] at {cert.h}')
 emit(f'  exact lt_of_lt_of_le (by norm_num) {cert.h}.1')
 pins=['hmu','hk']+[x+str(i) for i in range(3) for x in ['he','hve','hg']]+[f'hf{i}' for i in range(12)]+['hH']
 final=f'''/-- Actual certificate positivity throughout this entire rational box. -/
theorem {prefix}_positive {{qv : EdgeTriple}} (hq : qv ∈ {prefix}Box.region) :
    {q(target)} < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by'''
 source=header+cg.modularize('\n'.join(cg.lines),prefix,pins,final)+'\n\nend SparseLowerTail.Section05\n'
 (ROOT/f'lean/SparseLowerTail/Section05/CoverS1{tag}.lean').write_text(source)
