import SparseLowerTail.Section08.FamilyOffsetCover
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Endpoints0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def parameter1 : FamilyParameterCertificate := ⟨exp37,exp38,exp16,exp18,⟨185881438141090685,188535010275086213⟩⟩
theorem parameter1_valid : parameter1.Valid := by
  refine ⟨exp37_valid,exp38_valid,exp16_valid,exp18_valid,?_,?_,?_⟩
  all_goals decide +kernel
def coefficients1 : Fin 7 → DyadicInterval := ![⟨-27663035034909348,-26873499859813164⟩,⟨54533274605949748,56056527319560718⟩,⟨2202007373973087,2253429645700642⟩,⟨-4709954381086753,-4571401457931308⟩,⟨26692986759303920,27112585775914197⟩,⟨-53106423924191998,-51614649304787363⟩,⟨301384414201564295,305704123096940199⟩]
theorem coefficients1_checked : ∀i,(FamilyCoeff.coefficientExpr i).dyadicEval parameter1.parameterBox=some (coefficients1 i) := by
  intro i; fin_cases i <;> decide +kernel

end SparseLowerTail.Section08.FamilyABBReplay.Smoke
