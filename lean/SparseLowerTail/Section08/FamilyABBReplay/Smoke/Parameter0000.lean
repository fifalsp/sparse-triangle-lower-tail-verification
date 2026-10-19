import SparseLowerTail.Section08.FamilyOffsetCover
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Endpoints0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def parameter0 : FamilyParameterCertificate := ⟨exp36,exp37,exp17,exp19,⟨187483420576340702,190162297846372546⟩⟩
theorem parameter0_valid : parameter0.Valid := by
  refine ⟨exp36_valid,exp37_valid,exp17_valid,exp19_valid,?_,?_,?_⟩
  all_goals decide +kernel
def coefficients0 : Fin 7 → DyadicInterval := ![⟨-27770674008510050,-26974820695189849⟩,⟨54787675100396719,56323730049714611⟩,⟨2223059054073101,2275205846062502⟩,⟨-4734159318636921,-4594233856076890⟩,⟨26711806132411047,27134888770390998⟩,⟨-53402604796012274,-51896662886233548⟩,⟨301737708911472848,306088925965036039⟩]
theorem coefficients0_checked : ∀i,(FamilyCoeff.coefficientExpr i).dyadicEval parameter0.parameterBox=some (coefficients0 i) := by
  intro i; fin_cases i <;> decide +kernel

end SparseLowerTail.Section08.FamilyABBReplay.Smoke
