import SparseLowerTail.Section08.FamilyParameterTaylor
import SparseLowerTail.Section08.FamilyScaledSmoke

/-! Checked derivatives of all seven coefficients, through order three,
on L ∈ [39/10,2503/640]. These are real derivative enclosures, not a
complete exterior-region certificate. Numerical proposals are checked by
the kernel independently of the program that proposed them. -/
namespace SparseLowerTail.Certificate.FamilyParameterSmoke
open Numerics FamilyCoeff
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def intervals : Fin 4 → Fin 7 → DyadicInterval :=
  ![![⟨-27770674008510050,-26974820695189849⟩,⟨54787675100396719,56323730049714611⟩,⟨2223059054073101,2275205846062502⟩,⟨-4734159318636921,-4594233856076890⟩,⟨26711806132411047,27134888770390998⟩,⟨-53402604796012274,-51896662886233548⟩,⟨301737708911472848,306088925965036039⟩],
    ![⟨8708940502265045,10322576622097032⟩,⟨-25275857749686864,-22347954928414628⟩,⟨-2017017667088518,-1910876030261672⟩,⟨2001982953152642,2289744223763603⟩,⟨-2243785687175454,-1442150915651124⟩,⟨25003292260170330,27886540600533802⟩,⟨-37327572180173948,-29927124184886482⟩],
    ![⟨4815001836414273,8367659695100112⟩,⟨-9084774909803985,-2965521805024295⟩,⟨1012845786547991,1253522586561271⟩,⟨447778215061538,1083550430026266⟩,⟨-7683110678579670,-5759692884527915⟩,⟨-5418164383182569,461231576579032⟩,⟨-30560101380597389,-12919225762315656⟩],
    ![⟨-20046898879572057,-11574349245261473⟩,⟨20119134101480015,33994993825054953⟩,⟨216494740127004,814396337347346⟩,⟨-3933488043586643,-2414923431960096⟩,⟨5287453286783062,10775531243924190⟩,⟨-21683941479597276,-8628537558705902⟩,⟨10344084415629283,61891381030514191⟩]]

theorem intervals_checked (n : Fin 4) (i : Fin 7) :
    (derivativeExpr i n.val).dyadicEval FamilyScaledSmoke.Leaf0.parameter.parameterBox=
      some (intervals n i) := by
  fin_cases n <;> fin_cases i <;> decide +kernel

theorem derivative_contains (n : Fin 4) (i : Fin 7) {t : ℝ}
    (ht : Bounds t (39/10) (2503/640)) :
    (intervals n i).contains (coefficientDerivative i n.val t) := by
  apply coefficientDerivative_interval FamilyScaledSmoke.Leaf0.parameter
    FamilyScaledSmoke.Leaf0.parameter_valid i n.val (intervals_checked n i)
  norm_num [FamilyScaledSmoke.Leaf0.parameter,FamilyScaledSmoke.Leaf0.logLower,
    FamilyScaledSmoke.Leaf0.logUpper] at ⊢
  exact ht

end SparseLowerTail.Certificate.FamilyParameterSmoke
