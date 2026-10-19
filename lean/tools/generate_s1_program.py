#!/usr/bin/env python3
"""Generate an untrusted shared-register program, then prove its output identities."""
from pathlib import Path
from s1_expr_model import expr,partial
from generate_exp_endpoints import rat
E=expr();G=[partial(E,i)for i in range(3)];H=[[partial(G[i],j)for j in range(3)]for i in range(3)]
ids={};code=[]
def emit(e):
 if e in ids:return ids[e]
 op,*a=e.t
 if op=='c':s='.rational '+rat(a[0])
 elif op=='v':s='.var '+str(a[0])
 elif op=='-':s='.neg '+str(emit(a[0]))
 else:s=('.add 'if op=='+'else'.mul ')+str(emit(a[0]))+' '+str(emit(a[1]))
 k=len(code);code.append(s);ids[e]=k;return k
out=[emit(E)]+[emit(g)for g in G]+[emit(h)for row in H for h in row];depth=(len(code)-1).bit_length()
lines=['''import SparseLowerTail.Numerics.IntervalProgram
import SparseLowerTail.Section05.CoverS1CachedTaylor

/-! Shared-register program for the exact S1 value, gradient, and Hessian.
All thirteen symbolic output identities are kernel checked. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
''',f'def s1ProgramDepth : ℕ := {depth}','def s1Program : List (IntervalInstruction 9) :=\n  ['+',\n   '.join(code)+']']
labels=['Value']+[f'Gradient{i}'for i in range(3)]+[f'Hessian{i}{j}'for i in range(3)for j in range(3)]
targets=['s1CertificateExpr']+[f's1GradientData{i}'for i in range(3)]+[f's1HessianData{i}{j}'for i in range(3)for j in range(3)]
for label,k,target in zip(labels,out,targets):
 lines +=[f'def s1Program{label} : ℕ := {k}',f'theorem s1Program{label}_eq :\n    (IntervalProgram.symbolic s1Program s1ProgramDepth).get s1Program{label} = {target} := by\n  decide +kernel']
lines+=['end SparseLowerTail.Section05','']
Path('SparseLowerTail/Section05/CoverS1Program.lean').write_text('\n\n'.join(lines));print('instructions',len(code),'depth',depth,'outputs',out)
