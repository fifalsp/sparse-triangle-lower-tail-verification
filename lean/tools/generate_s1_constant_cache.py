#!/usr/bin/env python3
"""Generate literal dyadic constants, each conversion independently kernel checked."""
from pathlib import Path
from generate_s1_horner_data import expr,partial,horner
from generate_exp_endpoints import rat
E=expr();G=[horner(partial(E,i))for i in range(3)];H=[[horner(partial(partial(E,i),j))for j in range(3)]for i in range(3)]
lines=['''import SparseLowerTail.Section05.CoverS1HornerTaylor
import SparseLowerTail.Numerics.CachedPolynomial

/-! Pre-rounded constants for repeated S1 Taylor evaluation. Each conversion is
checked once; compositional validity proofs reuse those checked conversions. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
'''];ids={};scale=2**60;constants=0
def emit(e):
 global constants
 if e in ids:return ids[e]
 op,*a=e.t
 if op=='c':
  q=a[0];low=q.numerator*scale//q.denominator;up=-((-q.numerator*scale)//q.denominator)
  rhs=f'.rational {rat(q)} ⟨{low},{up}⟩';proof='by decide +kernel';constants+=1
 elif op=='v':rhs=f'.var {a[0]}';proof='True.intro'
 elif op=='-':
  child=emit(a[0]);rhs=f'.neg {child}';proof=f'{child}_valid'
 else:
  left,right=map(emit,a);rhs=f'{".add"if op=="+"else".mul"} {left} {right}';proof=f'⟨{left}_valid,{right}_valid⟩'
 name=f's1CachedNode{len(ids)}';ids[e]=name
 lines.extend([f'def {name} : CachedPolynomialExpr 9 := {rhs}',f'theorem {name}_valid : {name}.Valid := {proof}'])
 return name
items=[('Value',E,'s1CertificateExpr')]+[(f'Gradient{i}',G[i],f's1HornerGradient{i}')for i in range(3)]+[(f'Hessian{i}{j}',H[i][j],f's1HornerHessian{i}{j}')for i in range(3)for j in range(3)]
for tag,e,target in items:
 name=emit(e)
 lines.extend([f'def s1Cached{tag} : CachedPolynomialExpr 9 := {name}',f'theorem s1Cached{tag}_valid : s1Cached{tag}.Valid := {name}_valid',f'theorem s1Cached{tag}_erase : s1Cached{tag}.erase = {target} := by decide +kernel'])
lines.append('end SparseLowerTail.Section05\n')
Path('SparseLowerTail/Section05/CoverS1ConstantCache.lean').write_text('\n\n'.join(lines))
print('nodes',len(ids),'constants',constants)
