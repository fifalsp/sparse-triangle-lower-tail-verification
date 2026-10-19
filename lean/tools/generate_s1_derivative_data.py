#!/usr/bin/env python3
"""Propose shared symbolic derivative data, verified by Lean definitional equality."""
from pathlib import Path
from fractions import Fraction
from s1_expr_model import expr,partial
from generate_exp_endpoints import rat
E=expr();G=[partial(E,i) for i in range(3)];H=[[partial(G[i],j) for j in range(3)]for i in range(3)]
ids={};lines=['''import SparseLowerTail.Section05.CoverS1TaylorAxes

/-! Shared expanded derivative data. Every derivative identity is checked by
`decide +kernel`; these are exact syntax-level normal forms, not numerical approximations. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
''']
def emit(e):
 if e in ids:return ids[e]
 op,*a=e.t
 if op=='c':s='.rational '+rat(a[0])
 elif op=='v':s='.var '+str(a[0])
 elif op=='-':s='.neg '+emit(a[0])
 else:s=('.add 'if op=='+'else'.mul ')+emit(a[0])+' '+emit(a[1])
 name='s1DerivativeNode'+str(len(ids));ids[e]=name
 lines.append(f'def {name} : S1Expr := {s}')
 return name
GN=list(map(emit,G));HN=[list(map(emit,row))for row in H]
for i,name in enumerate(GN):lines +=[f'def s1GradientData{i} : S1Expr := {name}',f'theorem s1GradientData{i}_eq : s1Partial {i} = s1GradientData{i} := by decide +kernel']
for i,row in enumerate(HN):
 for j,name in enumerate(row):lines +=[f'def s1HessianData{i}{j} : S1Expr := {name}',f'theorem s1HessianData{i}{j}_eq : s1Partial2 {i} {j} = s1HessianData{i}{j} := by decide +kernel']
lines+=['end SparseLowerTail.Section05','']
Path('SparseLowerTail/Section05/CoverS1DerivativeData.lean').write_text('\n'.join(lines));print('shared nodes',len(ids))
