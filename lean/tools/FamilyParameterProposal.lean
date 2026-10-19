/-! Untrusted interval proposals. `FamilyParameterSmoke.intervals_checked`
checks the proposed integers using the kernel. Run from lean/: 
  lake env lean tools/FamilyParameterProposal.lean
-/
import SparseLowerTail.Section08.FamilyParameterCalculus
import SparseLowerTail.Section08.FamilyScaledSmoke
open SparseLowerTail SparseLowerTail.Certificate SparseLowerTail.Certificate.FamilyCoeff
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
#eval (List.range 4).map fun n => (List.finRange 7).map fun i =>
  (derivativeExpr i n).dyadicEval FamilyScaledSmoke.Leaf0.parameter.parameterBox
