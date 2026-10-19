import SparseLowerTail.Section08.FamilyOffsetCover
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Endpoints0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def parameter2 : FamilyParameterCertificate := ⟨exp52,exp53,exp1,exp2,⟨1519077207232295,3302880302495162⟩⟩
theorem parameter2_valid : parameter2.Valid := by
  refine ⟨exp52_valid,exp53_valid,exp1_valid,exp2_valid,?_,?_,?_⟩
  all_goals decide +kernel
def coefficients2 : Fin 7 → DyadicInterval := ![⟨-892234360248809,-347130172366755⟩,⟨653348102919254,1699912178103358⟩,⟨5030281172756,11093107810771⟩,⟨-83233558932595,-34205650731628⟩,⟨7070820970953583,8361120412598912⟩,⟨-1586088602454325,-605569326939405⟩,⟨125180261293206220,159328496344976349⟩]
theorem coefficients2_checked : ∀i,(FamilyCoeff.coefficientExpr i).dyadicEval parameter2.parameterBox=some (coefficients2 i) := by
  intro i; fin_cases i <;> decide +kernel

end SparseLowerTail.Section08.FamilyABBReplay.Smoke
