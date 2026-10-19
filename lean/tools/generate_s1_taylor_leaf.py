#!/usr/bin/env python3
"""One original S1 Taylor2 leaf. All claims are replayed in Lean."""
from pathlib import Path
from fractions import Fraction as F
from generate_exp_endpoints import endpoint,rat
from s1_expr_model import T,O,MU
lo=list(map(F,['47201/4096','47201/4096','20229/4096']));hi=list(map(F,['6743/512','6743/512','6743/1024']))
mid=[(a+b)/2 for a,b in zip(lo,hi)];rad=[(b-a)/2 for a,b in zip(lo,hi)]
vals=list(dict.fromkeys(lo+hi+mid));idx={q:i for i,q in enumerate(vals)}
lines=['''import SparseLowerTail.Section05.CoverS1TaylorBox
import SparseLowerTail.Numerics.ExpEndpoints
import SparseLowerTail.Section05.CoverConstantDigits

/-! First actual Taylor2 leaf for the original S1 certificate.
The parameter vertex and all coefficients remain the exact release data. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
''']
for i,q in enumerate(vals):
 qq,n,l,u,L,U=endpoint(q,20,60)
 lines += [f'def s1TaylorEndpoint{i} : ExpEndpointCertificate :=\n  ⟨{rat(qq)},{n},{rat(l)},{rat(u)},{rat(L)},{rat(U)}⟩',f'theorem s1TaylorEndpoint{i}_valid : s1TaylorEndpoint{i}.Valid := by decide +kernel']
lines += ['def s1TaylorLeafBox : LogBox := ⟨!['+','.join(rat(a) for a in lo)+'],!['+','.join(rat(a) for a in hi)+']⟩']
lines += ['def s1TaylorLeafData : S1TaylorBoxData :=\n  ⟨s1TaylorLeafBox,!['+','.join('s1TaylorEndpoint'+str(idx[a]) for a in lo)+'],!['+','.join('s1TaylorEndpoint'+str(idx[a]) for a in hi)+'],!['+','.join('s1TaylorEndpoint'+str(idx[a]) for a in mid)+']⟩']
for tag,arr in [('lower',lo),('upper',hi),('center',mid)]:
 lines += [f'theorem s1TaylorLeaf_{tag}_valid : ∀ i, (s1TaylorLeafData.{tag}Exp i).Valid := by\n  intro i\n  fin_cases i\n'+''.join(f'  · exact s1TaylorEndpoint{idx[a]}_valid\n' for a in arr)]
lines += ["""theorem s1Taylor_rational_check : (1/100:ℚ) < s1TaylorLeafData.margin := by
  decide +kernel

/-- Actual certified positivity on a full original Taylor2 leaf, not merely
on sampled points or on a conditional interval enclosure. -/
theorem coverS1_taylor_leaf_positive {q : EdgeTriple} (hq : q ∈ s1TaylorLeafBox.region) :
    (1/100:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  have h := s1TaylorLeafData.positive s1TaylorLeaf_lower_valid s1TaylorLeaf_upper_valid
    s1TaylorLeaf_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s1Taylor_rational_check hq
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

end SparseLowerTail.Section05
"""]
Path('SparseLowerTail/Section05/CoverS1TaylorLeaf.lean').write_text('\n\n'.join(lines))
