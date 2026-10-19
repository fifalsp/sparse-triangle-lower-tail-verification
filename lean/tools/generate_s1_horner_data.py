#!/usr/bin/env python3
"""Propose exact Horner derivative polynomials; Lean verifies every rewrite by ring.
Requires sympy only for generating data, not for checking any theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import sympy as s
from s1_expr_model import expr,partial,c,v
from generate_exp_endpoints import rat
vrs=s.symbols('v0:9')
@lru_cache(None)
def tos(e):
 op,*a=e.t
 if op=='c':return s.Rational(a[0].numerator,a[0].denominator)
 if op=='v':return vrs[a[0]]
 if op=='-':return -tos(a[0])
 if op=='+':return tos(a[0])+tos(a[1])
 return tos(a[0])*tos(a[1])
@lru_cache(None)
def froms(z):
 if z.is_Rational:return c(F(int(z.p),int(z.q)))
 if z.is_Symbol:return v(vrs.index(z))
 if z.is_Add or z.is_Mul:
  parts=list(map(froms,z.args));out=parts[0]
  for a in parts[1:]:out=out+a if z.is_Add else out*a
  return out
 if z.is_Pow:return froms(z.args[0])**int(z.args[1])
 raise ValueError(z)
def horner(z):return froms(s.horner(tos(z),*vrs[3:],*vrs[:3]))
def lean(z):
 op,*a=z.t
 if op=='c':return f'(.rational {rat(a[0])})'
 if op=='v':return f'(.var {a[0]})'
 if op=='-':return f'(.neg {lean(a[0])})'
 return f'({".add"if op=="+"else".mul"} {lean(a[0])} {lean(a[1])})'
def real(z):
 op,*a=z.t
 if op=='c':return f'({rat(a[0])} : ℝ)'
 if op=='v':return f'x {a[0]}'
 if op=='-':return f'(-{real(a[0])})'
 return f'({real(a[0])}{"+"if op=="+"else"*"}{real(a[1])})'
def main():
 E=expr();G=[partial(E,i)for i in range(3)];H=[[partial(G[i],j)for j in range(3)]for i in range(3)]
 lines=['''import SparseLowerTail.Section05.CoverS1CachedTaylor

/-! Exact Horner forms of S1 derivative polynomials. The CAS proposes expressions;
all twelve real-polynomial identities below are proved by Lean's ring tactic. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
''']
 for kind,z,name in [('Gradient',G[i],str(i))for i in range(3)]+[('Hessian',H[i][j],f'{i}{j}')for i in range(3)for j in range(3)]:
  opt=horner(z);new='s1Horner'+kind+name;old='s1'+kind+'Data'+name
  lines += [f'def {new} : S1Expr := '+lean(opt),f'theorem {new}_eq (x : Fin 9 → ℝ) :\n    {new}.realEval x = {old}.realEval x := by\n  change '+real(opt)+' = '+real(z)+'\n  norm_num\n  ring']
 lines += ['''def s1HornerGradient : Fin 3 → S1Expr :=
  ![s1HornerGradient0,s1HornerGradient1,s1HornerGradient2]
def s1HornerHessian : Fin 3 → Fin 3 → S1Expr :=
  ![![s1HornerHessian00,s1HornerHessian01,s1HornerHessian02],
    ![s1HornerHessian10,s1HornerHessian11,s1HornerHessian12],
    ![s1HornerHessian20,s1HornerHessian21,s1HornerHessian22]]

theorem s1HornerGradient_eq (i : Fin 3) (x : Fin 9 → ℝ) :
    (s1HornerGradient i).realEval x = (s1Partial i).realEval x := by
  rw [s1GradientExpressions_eq]
  fin_cases i
  · exact s1HornerGradient0_eq x
  · exact s1HornerGradient1_eq x
  · exact s1HornerGradient2_eq x

theorem s1HornerHessian_eq (i j : Fin 3) (x : Fin 9 → ℝ) :
    (s1HornerHessian i j).realEval x = (s1Partial2 i j).realEval x := by
  rw [s1HessianExpressions_eq]
  fin_cases i <;> fin_cases j
'''+''.join(f'  · exact s1HornerHessian{i}{j}_eq x\n'for i in range(3)for j in range(3))+'''
end SparseLowerTail.Section05
''']
 Path('SparseLowerTail/Section05/CoverS1HornerData.lean').write_text('\n\n'.join(lines))
if __name__=='__main__':main()
