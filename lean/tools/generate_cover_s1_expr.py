#!/usr/bin/env python3
"""Reify the exact original S1 vertex-zero polynomial, not floating-point fit."""
from pathlib import Path
import json
from fractions import Fraction
root=Path(__file__).resolve().parents[2]
c=json.loads((root/'data/cover.json').read_text())['cells']['S1']
def rat(s):
 f=Fraction(s);return f'({f.numerator}/{f.denominator} : ℚ)'
out=['''import SparseLowerTail.Numerics.IntervalExpr
import SparseLowerTail.Section05.CoverS1FirstBox

/-! A reified exact polynomial for the S1 vertex-zero logarithmic certificate.
Variables 0–2 are q; 3–5 are exp(-q); 6,7,8 are t*, Ω*, and μ.
This is a symbolic identity. Numeric positivity requires a separate checked box. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev S1Expr := PolynomialExpr 9
def s1Log (i : Fin 3) : S1Expr := -(.var (i.castAdd 6))
def s1Edge (i : Fin 3) : S1Expr := .var ⟨i.val+3,by omega⟩
def s1Entropy (i : Fin 3) : S1Expr := s1Edge i*s1Log i-s1Edge i+1
def s1VertexEntropy (i : Fin 3) : S1Expr := s1Edge i*s1Log i-2*s1Edge i+2
def s1Observable (i : Fin 3) : S1Expr := s1Edge i+.var 7*s1Entropy i
def s1Average (a b c : S1Expr) : S1Expr := (a+b+c)*.rational (1/3)
''']
out += [f'def s1M : ℚ := {rat(c["vertices"][0][0])}',f'def s1F : ℚ := {rat(c["vertices"][0][1])}',f'def s1Lambda : ℚ := {rat(c["lam"])}', 'def s1Theta : Fin 12 → ℚ := !['+','.join(rat(x) for x in c['theta'])+']', 'def s1VertexMean : S1Expr := 1+.rational s1F-.rational s1M']
out += ['def s1EdgeTest (j : Fin 5) (i : Fin 3) : S1Expr :=\n  ![1,s1Edge i,s1Edge i^2,s1Edge i^3,s1Edge i*s1Log i] j', 'def s1VertexTest (j : Fin 4) (i : Fin 3) : S1Expr :=\n  ![s1Edge i,s1Edge i^3,s1Edge i^4,s1Edge i*s1Log i] j']
for typ in ['Edge','Vertex']:
 terms=[]
 for i in range(3):
  j,k=(i+1)%3,(i+2)%3
  res=f'(s1Log {i}+.var 8*s1Edge {j}*s1Edge {k})' if typ=='Edge' else f'(s1VertexEntropy {j}+s1VertexEntropy {k}-2*s1VertexMean)'
  terms.append(f'(s1{typ}Test j {i}*{res})')
 out += [f'def s1{typ}Residual (j : Fin {5 if typ=="Edge" else 4}) : S1Expr :=\n  s1Average '+ ' '.join(terms)]
features=['s1Average (s1Edge 0) (s1Edge 1) (s1Edge 2)-.rational s1M','s1Edge 0*s1Edge 1*s1Edge 2-.var 6','s1Average (s1Entropy 0) (s1Entropy 1) (s1Entropy 2)-.rational s1F']+[f's1EdgeResidual {j}' for j in range(5)]+[f's1VertexResidual {j}' for j in range(4)]
out+=['def s1Feature (i : Fin 12) : S1Expr :=\n  !['+',\n    '.join(features)+'] i', '''def s1Hoeffding : S1Expr :=
  s1Average (s1Observable 0^2) (s1Observable 1^2) (s1Observable 2^2)-
  2*s1Average (s1Observable 0*s1Observable 1) (s1Observable 1*s1Observable 2)
    (s1Observable 2*s1Observable 0)+(.rational s1M+.var 7*.rational s1F)^2

def s1CertificateExpr : S1Expr :=
  -(''']
s='0'
for i in reversed(range(12)):s=f'.rational (s1Theta {i})*s1Feature {i}+({s})'
out[-1]+=s+')-.rational s1Lambda*s1Hoeffding\n'
out+=['''noncomputable def s1Environment (q : EdgeTriple) : Fin 9 → ℝ :=
  ![q.1.1,q.1.2,q.2,Real.exp (-q.1.1),Real.exp (-q.1.2),Real.exp (-q.2),
    criticalTriangle,criticalOmega,relaxationMultiplier coverS1Vertex0]

@[simp] theorem s1Log_realEval (i : Fin 3) (q : EdgeTriple) :
    (s1Log i).realEval (s1Environment q) = -(![q.1.1,q.1.2,q.2] i) := by
  fin_cases i <;> rfl

@[simp] theorem s1Edge_realEval (i : Fin 3) (q : EdgeTriple) :
    (s1Edge i).realEval (s1Environment q) = Real.exp (-(![q.1.1,q.1.2,q.2] i)) := by
  fin_cases i <;> rfl

@[simp] theorem s1Average_realEval (a b c : S1Expr) (x : Fin 9 → ℝ) :
    (s1Average a b c).realEval x = (a.realEval x+b.realEval x+c.realEval x)/3 := by
  simp only [s1Average,realEval_mul,realEval_add,realEval_rational]
  norm_num
  ring

@[simp] theorem s1Feature_realEval (i : Fin 12) (q : EdgeTriple) :
    (s1Feature i).realEval (s1Environment q) =
      certificateFeature i (logBoxEdges q) coverS1Vertex0 := by
  fin_cases i <;>
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

@[simp] theorem s1Hoeffding_realEval (q : EdgeTriple) :
    s1Hoeffding.realEval (s1Environment q) =
      certificateHoeffding (logBoxEdges q) coverS1Vertex0 := by
  simp only [s1Hoeffding,s1Observable,s1Entropy,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
    realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
    realEval_rational,realEval_var,Matrix.cons_val]
  simp only [s1Environment,certificateHoeffding,cyclicAverage,coverCycle,logBoxEdges,
    criticalObservable,entropy,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp]
  norm_num
  ring

/-- Exact symbolic identity with the certificate from the paper and data file. -/
theorem s1CertificateExpr_realEval (q : EdgeTriple) :
    s1CertificateExpr.realEval (s1Environment q) =
      logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  rw [logCertificate,coverCertificate_fin12_expansion]
  simp only [s1CertificateExpr,realEval_sub,realEval_neg,realEval_add,realEval_mul,
    s1Feature_realEval,s1Hoeffding_realEval,realEval_zero,realEval_one,realEval_two,realEval_rational,realEval_var]
  simp only [s1Theta,s1Lambda,coverS1Theta,coverS1Lam,Matrix.cons_val]
  norm_num

end SparseLowerTail.Section05
''']
source='\n'.join(out)
a=source.index('@[simp] theorem s1Feature_realEval')
b=source.index('@[simp] theorem s1Hoeffding_realEval')
base=source[a:b]
pieces=[]
for i in range(12):
 x=base.replace('@[simp] theorem s1Feature_realEval (i : Fin 12) (q : EdgeTriple)',f'theorem s1Feature{i}_realEval (q : EdgeTriple)').replace('s1Feature i',f's1Feature {i}').replace('certificateFeature i',f'certificateFeature {i}').replace('  fin_cases i <;>\n','')
 pieces.append(x)
pieces.append("@[simp] theorem s1Feature_realEval (i : Fin 12) (q : EdgeTriple) :\n    (s1Feature i).realEval (s1Environment q) =\n      certificateFeature i (logBoxEdges q) coverS1Vertex0 := by\n  fin_cases i\n"+''.join(f'  · exact s1Feature{j}_realEval q\n' for j in range(12))+'\n')
source=source[:a]+''.join(pieces)+source[b:]
source=source.replace('  norm_num\n  ring\n\n/-- Exact symbolic','  norm_num\n\n/-- Exact symbolic')
source=source.replace('set_option linter.unusedSimpArgs false','set_option linter.unusedSimpArgs false\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option linter.unnecessarySeqFocus false')
(root/'lean/SparseLowerTail/Section05/CoverS1Expr.lean').write_text(source)
