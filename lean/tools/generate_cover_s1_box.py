#!/usr/bin/env python3
"""Generate a proof for one genuine cover box, not a full cover certificate.
All input rationals come from data/cover.json. This generator is untrusted:
Lean checks every interval operation and the reduction to the actual Ψ.
"""
from fractions import Fraction as F
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[2]
cell=json.loads((ROOT/'data/cover.json').read_text())['cells']['S1']
lines=[]
def emit(s=''):lines.append(s)
def q(x):
 x=F(x)
 return f'({x.numerator}/{x.denominator} : ℝ)' if x.denominator!=1 else f'({x.numerator} : ℝ)'
def outward(l,u):
 scale=10**10
 return F(l.numerator*scale//l.denominator,scale),F(-((-u.numerator*scale)//u.denominator),scale)
class Node:
 count=0
 def __init__(self,e,l,u,h):self.e,self.l,self.u,self.h=e,F(l),F(u),h
 @staticmethod
 def c(x):return Node(q(x),x,x,f'(Bounds.refl {q(x)})')
 def op(self,b,op):
  if op=='+':l,u=self.l+b.l,self.u+b.u;pr=f'{self.h}.add {b.h}'
  elif op=='-':l,u=self.l-b.u,self.u-b.l;pr=f'{self.h}.sub {b.h}'
  elif op=='*':
   corners=[self.l*b.l,self.l*b.u,self.u*b.l,self.u*b.u];l,u=min(corners),max(corners)
   l,u=outward(l,u)
   pr=f'{self.h}.mul_corners {b.h} '+' '.join(['(by norm_num)']*8)
  elif op=='/':
   assert self.l>=0 and b.l>0
   l,u=self.l/b.u,self.u/b.l;pr=f'{self.h}.div_pos {b.h} (by norm_num) (by norm_num)'
  l,u=outward(l,u)
  Node.count+=1;n=f'v{Node.count}';h=f'h{Node.count}'
  emit(f'  let {n} : ℝ := {self.e}{op}{b.e}')
  emit(f'  have {h} : Bounds {n} {q(l)} {q(u)} := by')
  if op=='*':emit(f'    exact {pr}')
  else:emit(f'    exact ({pr}).weaken (by norm_num) (by norm_num)')
  return Node(n,l,u,h)
 def __add__(s,b):return s.op(b,'+')
 def __sub__(s,b):return s.op(b,'-')
 def __mul__(s,b):return s.op(b,'*')
 def __truediv__(s,b):return s.op(b,'/')
 def neg(s):return Node.c(0)-s
 def pow(s,n):
  if n==0:return Node.c(1)
  r=s
  for _ in range(n-1):r=r*s
  return r
 def pin(s,e,name,unfolds=''):
  emit(f'  have {name} : Bounds ({e}) {q(s.l)} {q(s.u)} := by')
  emit(f'    convert {s.h} using 1 <;>')
  emit('      simp only ['+','.join(['certificateFeature','cyclicAverage','coverEdgeResidual','coverVertexResidual','edgeTest','vertexTest','coverCycle','logBoxEdges','coverS1Vertex0','relaxationMultiplier','relaxationVertexMean','entropy','vertexEntropy','criticalObservable','certificateHoeffding','Matrix.cons_val','Matrix.cons_val_zero','Matrix.cons_val_succ',"Matrix.cons_val_zero'","Matrix.cons_val_succ'"]+[f'v{i}' for i in range(1,Node.count+1)])+'] <;> ring')
  return Node(f'({e})',s.l,s.u,name)
 def nonneg(s,h):
  if s.l>=0:return s
  emit(f'  have {s.h}p : Bounds {s.e} 0 {q(s.u)} := ⟨{h},{s.h}.2⟩')
  return Node(s.e,0,s.u,s.h+'p')

emit('import SparseLowerTail.Section05.CoverConstantBounds\nimport SparseLowerTail.Section05.SortedLogBoxes')
emit('''
/-! First actual proof-producing non-apex cover calculation.
Stable manuscript anchor `prop:cover`, cell S1, first printed parameter vertex.
The exact original dyadic coefficients are read from data/cover.json.
This proves positivity ONLY on 0 ≤ qᵢ ≤ 1/1024. The rest of S1 and every
other cell still require checked partitions; this is not the full cover theorem.
Regenerate from lean/ with python3 tools/generate_cover_s1_box.py. -/
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
''')
expansion='0'
for i in reversed(range(12)):expansion=f'(θ {i}*certificateFeature {i} u π+{expansion})'
emit(f'''theorem coverCertificate_fin12_expansion (θ : Fin 12 → ℝ) (lam : ℝ)
    (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam u π = -{expansion}-lam*certificateHoeffding u π := by
  unfold coverCertificate
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  rfl
''')
emit('def coverS1Theta : Fin 12 → ℝ := !['+','.join(q(t) for t in cell['theta'])+']')
emit('def coverS1Lam : ℝ := '+q(cell['lam']))
emit('def coverS1Q : ℝ := '+q(cell['Q']))
m,Fv=map(F,cell['vertices'][0]);emit(f'def coverS1Vertex0 : ℝ × ℝ := ({q(m)},{q(Fv)})')
emit('''
/-- Elementary exponential enclosure, uniform on the entire first dyadic box. -/
theorem exp_neg_first_box {x : ℝ} (hx : x ∈ Set.Icc 0 (1/1024 : ℝ)) :
    Bounds (Real.exp (-x)) (1023/1024) 1 := by
  constructor
  · have h := Real.add_one_le_exp (-x)
    linarith [hx.2]
  · simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (neg_nonpos.mpr hx.1))

/-- A fully checked uniform positive lower bound for the actual S1 certificate
on a three-dimensional box, not merely at one sample point. -/
theorem coverS1_vertex0_first_box {qv : EdgeTriple}
    (hq : qv ∈ logCube (1/1024)) :
    3 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
''')
one=Node.c(1);two=Node.c(2);threeinv=Node.c(F(1,3));zero=Node.c(0)
T=Node('criticalTriangle',F(9217366,10**9),F(9217368,10**9),'criticalTriangle_checked_bounds')
O=Node('criticalOmega',0,2,'criticalOmega_coarse_bounds')
M=Node.c(m);C=Node.c(Fv)
mu=((one-C)-M)/T;mu=mu.pin('relaxationMultiplier coverS1Vertex0','hmu')
k=(one+C)-M;k=k.pin('relaxationVertexMean coverS1Vertex0','hk')
xs=[Node(f'(Real.exp (-{s}))',F(1023,1024),1,h) for s,h in [('qv.1.1','hx'),('qv.1.2','hy'),('qv.2','hz')]]
logs=[Node(f'(Real.log {x.e})',F(-1,1024),0,h) for x,h in zip(xs,['hlx','hly','hlz'])]
mullogs=[x*l for x,l in zip(xs,logs)]
entropies=[];vs=[];gs=[]
for i,(x,ml) in enumerate(zip(xs,mullogs)):
 h=(ml-x)+one;h=h.pin(f'entropy {x.e}',f'he{i}')
 h=h.nonneg(f'entropy_nonneg (le_of_lt (Real.exp_pos _))');entropies.append(h)
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
print('certificate enclosure',float(cert.l),float(cert.u),'nodes',Node.count)
emit(f'  have heq : {cert.e} = logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by')
# only unfold final summation arithmetic vars, not underlying feature calculations
names=[]
# final expression needs unfold nodes of s and terms; use dsimp on all defs (Lean only expands what occurs)
emit('    dsimp only ['+','.join(f'v{i}' for i in range(1,Node.count+1))+']')
emit('    rw [logCertificate,coverCertificate_fin12_expansion]')
emit('    simp only [coverS1Theta,coverS1Lam,Matrix.cons_val]')
emit('    ring')
emit(f'  rw [heq] at {cert.h}')
emit(f'  exact lt_of_lt_of_le (by norm_num) {cert.h}.1')
emit('\nend SparseLowerTail.Section05')

# Keep the generated proof DAG modular. Large let/have contexts can make Lean's
# elaboration expensive; each pinned analytic quantity is checked separately.
import re
source='\n'.join(lines)+'\n'
start=source.index('/-- A fully checked uniform')
header=source[:start]
body=source[source.index('  have hx :=',start):source.rindex('\nend SparseLowerTail.Section05')]
pat=re.compile(r'^  (?:have|let) (\w+)\b',re.M)
starts=list(pat.finditer(body));blocks={}
for i,mt in enumerate(starts):
 blocks[mt.group(1)]=body[mt.start():starts[i+1].start() if i+1<len(starts) else len(body)].rstrip()
order=list(blocks)
pins=['hmu','hk']+[n for n in order if re.fullmatch(r'he\d+|hve\d+|hg\d+|hf\d+|hH',n)]
known=set();out=[header]
def needed(name,root):
 if name in known and name!=root:return {name}
 text=blocks[name]
 text='\n'.join(l for l in text.splitlines() if not re.match(r'\s*(?:(?:simp|dsimp) only|norm_num \[)',l))
 ds={n for n in re.findall(r'\b\w+\b',text) if n in blocks and n!=name}
 res={name}
 for dep in ds:res |= needed(dep,root)
 return res
def trim(block,uses):
 # Remove unnecessary let definitions from simplification argument lists.
 for name in order:
  if name.startswith('v') and name not in uses:
   block=re.sub(r'(?<=[\[,])'+name+r'(?=[,\]])','',block)
 block=re.sub(r',+',',',block).replace('[,','[').replace(',]',']')
 return block
for name in pins:
 uses=needed(name,name)
 goal=blocks[name].splitlines()[0].split(' : ',1)[1].rsplit(' := by',1)[0]
 out.append(f'theorem coverS1_{name}_bounds {{qv : EdgeTriple}} (hq : qv ∈ logCube (1/1024)) :\n    {goal} := by')
 for dep in order:
  if dep not in uses:continue
  if dep in known:
   out.append(f'  have {dep} := coverS1_{dep}_bounds hq')
  else:out.append(trim(blocks[dep],uses))
 out.append(f'  exact {name}\n')
 known.add(name)
# The final small assembly depends on the feature bounds, not their full proofs.
uses=needed('heq','heq')
out.append('''/-- A checked bound on a genuine non-apex certificate throughout a 3D box.
This certifies one subdomain, not the complete S1 cube or twelve-cell cover. -/
theorem coverS1_vertex0_first_box {qv : EdgeTriple}
    (hq : qv ∈ logCube (1/1024)) :
    3 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by''')
for dep in order:
 if dep not in uses:continue
 if dep in known:out.append(f'  have {dep} := coverS1_{dep}_bounds hq')
 else:out.append(trim(blocks[dep],uses))
out.append('''
/-- The checked box is a subdomain of the actual S1 logarithmic support cube. -/
theorem coverS1_first_box_subset : logCube (1/1024) ⊆ logCube coverS1Q := by
  rintro q ⟨hx,hy,hz⟩
  have hQ : (1/1024 : ℝ) ≤ coverS1Q := by norm_num [coverS1Q]
  exact ⟨⟨hx.1,hx.2.trans hQ⟩,⟨hy.1,hy.2.trans hQ⟩,⟨hz.1,hz.2.trans hQ⟩⟩

/-- The actual S1 certificate is uniformly positive near (1,1,1), expressed
in the original edge coordinates. The full support cube is much larger. -/
theorem coverS1_vertex0_near_one :
    ∀ u ∈ edgeCube (Real.exp (-(1/1024 : ℝ))),
      3 ≤ coverCertificate coverS1Theta coverS1Lam u coverS1Vertex0 := by
  apply coverCertificate_bound_of_orderedLog
  intro q hq
  exact le_of_lt (coverS1_vertex0_first_box (orderedLogDomain_subset_cube _ hq))
''')
out.append('\nend SparseLowerTail.Section05')
(ROOT/'lean/SparseLowerTail/Section05/CoverS1FirstBox.lean').write_text('\n'.join(out)+'\n')
