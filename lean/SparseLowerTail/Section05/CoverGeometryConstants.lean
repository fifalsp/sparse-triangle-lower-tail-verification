import SparseLowerTail.Section05.CoverGeometryData

/-! Kernel-checked apex bounds sufficient for exact planar coverage. -/
noncomputable section
namespace SparseLowerTail.Section05.CoverGeometry
open Section04 Numerics

/-- A deliberately broad apex box, still strictly below the top fan vertices. -/
theorem criticalPoint_box :
    (4331/10000:ℝ)≤criticalMean ∧ criticalMean≤4333/10000 ∧
    (4627/10000:ℝ)≤criticalCost ∧ criticalCost≤4627799/10000000 := by
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

  have hm : Bounds criticalMean (4331/10000) (4333/10000) := by
    change Bounds ((criticalA+criticalB)/2) _ _
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have hc : criticalCost=(entropy criticalA+entropy criticalB)/2 := by
    exact critical_pair_cost.symm
  rw [hc]
  exact ⟨hm.1,hm.2,by linarith [hea.1,heb.1],by linarith [hea.2,heb.2]⟩

end SparseLowerTail.Section05.CoverGeometry
