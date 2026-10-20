import SparseLowerTail.Section08.FamilyAAACover

/-! The exact binary64 radius in Appendix A.3. The existing five AAA
Hessian certificates have enough geometric padding for this larger cube. -/
noncomputable section
namespace SparseLowerTail.Certificate.ManuscriptFamilyRadius
open Numerics Section04 Set

/-- The binary64 value of 0.1, written as its exact rational value. -/
def binary64Radius : ℝ := 3602879701896397/36028797018963968

theorem binary64Radius_pos : 0 < binary64Radius := by
  norm_num [binary64Radius]

theorem binary64Radius_error :
    binary64Radius - 1/10 = 1/180143985094819840 := by
  norm_num [binary64Radius]

theorem tenth_lt_binary64Radius : (1/10 : ℝ) < binary64Radius := by
  norm_num [binary64Radius]

/-- It lies within half a binary64 spacing of 1/10 in its binade. -/
theorem binary64Radius_half_ulp :
    |binary64Radius - 1/10| < 1/144115188075855872 := by
  norm_num [binary64Radius]

namespace AAA0
open FamilyAAACover.Leaf0
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10 : ℚ) (17/4 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius) :
    ∀i,Bounds (q i) (489313/125000 : ℚ) (113231/25000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤binary64Radius at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  norm_num only [binary64Radius] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10 : ℚ) (17/4 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end AAA0

namespace AAA1
open FamilyAAACover.Leaf1
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (17/4 : ℚ) (23/5 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius) :
    ∀i,Bounds (q i) (66206/15625 : ℚ) (4835057/1000000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤binary64Radius at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  norm_num only [binary64Radius] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (17/4 : ℚ) (23/5 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end AAA1

namespace AAA2
open FamilyAAACover.Leaf2
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (23/5 : ℚ) (53/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius) :
    ∀i,Bounds (q i) (284149/62500 : ℚ) (220349/40000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤binary64Radius at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  norm_num only [binary64Radius] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (23/5 : ℚ) (53/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end AAA2

namespace AAA3
open FamilyAAACover.Leaf3
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (53/10 : ℚ) (67/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius) :
    ∀i,Bounds (q i) (5213079/1000000 : ℚ) (6867561/1000000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤binary64Radius at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  norm_num only [binary64Radius] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (53/10 : ℚ) (67/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end AAA3

namespace AAA4
open FamilyAAACover.Leaf4
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (67/10 : ℚ) (19/2 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius) :
    ∀i,Bounds (q i) (6601003/1000000 : ℚ) (4811723/500000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤binary64Radius at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  norm_num only [binary64Radius] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (67/10 : ℚ) (19/2 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end AAA4

/-- The full AAA Hessian conclusion on the manuscript's closed cube. -/
theorem aaa_hessian_positive {z : ℝ} (hz : 0 < z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q ∈ familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v ≠ 0) : 0 < familyHessianForm z q v := by
  rcases FamilyAAACover.parameter_covered hL with h | h | h | h | h
  · exact AAA0.hessian_positive hz h hq hv
  · exact AAA1.hessian_positive hz h hq hv
  · exact AAA2.hessian_positive hz h hq hv
  · exact AAA3.hessian_positive hz h hq hv
  · exact AAA4.hessian_positive hz h hq hv

/-- The full AAA local minimum and exact zero at the manuscript's radius. -/
theorem aaa_local_nonnegative_and_unique_zero {z : ℝ} (hz : 0 < z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q ∈ familyCube (familyContactAAA z) binary64Radius) :
    0 ≤ familyPhi z q ∧ (familyPhi z q = 0 ↔ q = familyContactAAA z) := by
  have hz40 := FamilyAAACover.z_le_one_fortieth hz hL
  have hz1 : z < 1 := by linarith
  exact familyContactAAA_local hz hz1 (gamma_branch_neg hz hz40).ne
    binary64Radius_pos.le (fun _ hq _ hv => aaa_hessian_positive hz hL hq hv) hq

end SparseLowerTail.Certificate.ManuscriptFamilyRadius
