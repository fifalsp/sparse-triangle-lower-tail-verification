import SparseLowerTail.Section05.ApexTangencyExpressions
import SparseLowerTail.Section05.CoverConstantDigits

/-! Bounds on the nine actual apex primitives. Rational endpoints are derived
from proved transition digits and logarithm bounds, never assumed. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04 Numerics

def apexPrimitiveBounds : Fin 9 → RationalInterval :=
  ![⟨407254281156/100000000000,407254281216/100000000000⟩,⟨16328752549/100000000000,16328752562/100000000000⟩,⟨425850477/25000000000,1703401909/100000000000⟩,⟨8493469443/10000000000,2123367361/2500000000⟩,⟨9217366866/1000000000000,9217366881/1000000000000⟩,⟨92312137/100000000,92312139/100000000⟩,⟨1128627816/100000000,1128627817/100000000⟩,⟨43319048169/100000000000,43319048175/100000000000⟩,⟨4627797517/10000000000,4627797520/10000000000⟩]

theorem apexPrimitiveBounds_contains (i : Fin 9) :
    (apexPrimitiveBounds i).contains (apexPrimitiveValues i) := by
  have ha : Bounds criticalA (425850477/25000000000 : ℝ) (1703401909/100000000000 : ℝ) := transition_digits.1.weaken (by norm_num) (by norm_num)
  have hb : Bounds criticalB (8493469443/10000000000 : ℝ) (2123367361/2500000000 : ℝ) := transition_digits.2.1.weaken (by norm_num) (by norm_num)
  have hla := ha.log_of_endpoints (by norm_num) cover_logA_lower_endpoint.1 cover_logA_upper_endpoint.2
  have hlb := hb.log_of_endpoints (by norm_num) cover_logB_lower_endpoint.1 cover_logB_upper_endpoint.2
  have hma : Bounds (criticalA*Real.log criticalA) (-693717720070253137458353/10000000000000000000000000 : ℝ) (-21678678736343557300827/312500000000000000000000 : ℝ) := by
    exact ha.mul_corners hla (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hea : Bounds (entropy criticalA) (9135942089029746862541647/10000000000000000000000000 : ℝ) (285498190301156442699173/312500000000000000000000 : ℝ) := by
    convert (hma.sub ha).add (Bounds.refl 1) using 1 <;> norm_num [entropy]
  have hmb : Bounds (criticalB*Real.log criticalB) (-17335970117537193723663/125000000000000000000000 : ℝ) (-138687760823941207597527/1000000000000000000000000 : ℝ) := by
    exact hb.mul_corners hlb (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heb : Bounds (entropy criticalB) (1495661832462806276337/125000000000000000000000 : ℝ) (11965294876058792402473/1000000000000000000000000 : ℝ) := by
    convert (hmb.sub hb).add (Bounds.refl 1) using 1 <;> norm_num [entropy]

  have ht := criticalTriangle_sharp_bounds
  have ho := criticalOmega_checked_bounds
  have hmu : Bounds (relaxationMultiplier criticalPoint)
      (1128627816/100000000) (1128627817/100000000) := by
    rw [criticalMultiplier_eq_branchMu]
    convert transition_digits.2.2.1 using 1 <;> norm_num
  have hm : criticalMean=(criticalA+criticalB)/2 := rfl
  have hf : criticalCost=(entropy criticalA+entropy criticalB)/2 := critical_pair_cost.symm
  fin_cases i
  · change Bounds (-Real.log criticalA) ((407254281156/100000000000 : ℚ) : ℝ) ((407254281216/100000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [hla.1,hla.2]
  · change Bounds (-Real.log criticalB) ((16328752549/100000000000 : ℚ) : ℝ) ((16328752562/100000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [hlb.1,hlb.2]
  · change Bounds (criticalA) ((425850477/25000000000 : ℚ) : ℝ) ((1703401909/100000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [ha.1,ha.2]
  · change Bounds (criticalB) ((8493469443/10000000000 : ℚ) : ℝ) ((2123367361/2500000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [hb.1,hb.2]
  · change Bounds (criticalTriangle) ((9217366866/1000000000000 : ℚ) : ℝ) ((9217366881/1000000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [ht.1,ht.2]
  · change Bounds (criticalOmega) ((92312137/100000000 : ℚ) : ℝ) ((92312139/100000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [ho.1,ho.2]
  · change Bounds (relaxationMultiplier criticalPoint) ((1128627816/100000000 : ℚ) : ℝ) ((1128627817/100000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith [hmu.1,hmu.2]
  · change Bounds (criticalMean) ((43319048169/100000000000 : ℚ) : ℝ) ((43319048175/100000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    rw [hm]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  · change Bounds (criticalCost) ((4627797517/10000000000 : ℚ) : ℝ) ((4627797520/10000000000 : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    rw [hf]
    constructor <;> linarith [hea.1,hea.2,heb.1,heb.2]

def apexPrimitiveIntervals (i : Fin 9) : DyadicInterval :=
  DyadicInterval.ofRational (apexPrimitiveBounds i)

theorem apexPrimitiveIntervals_contains (i : Fin 9) :
    (apexPrimitiveIntervals i).contains (apexPrimitiveValues i) :=
  DyadicInterval.ofRational_contains (apexPrimitiveBounds_contains i)

end SparseLowerTail.Section05
