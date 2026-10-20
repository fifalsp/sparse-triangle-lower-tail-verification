import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Leaves3389
import SparseLowerTail.Section08.FamilyHessianRadiusTransfer

/-! Generated proposals; every numerical assertion is checked by Lean. -/
namespace SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate SparseLowerTail.Section04
open SparseLowerTail.Certificate.HessianRadiusTransfer
open SparseLowerTail.Section08.FamilyABBReplay.Smoke
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem padded_margins108451 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate108451.hessianIntervals) transform108451) := by
  decide +kernel

theorem small_coefficients108451 : ∀j,SmallCoefficient (box108451.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact108451 : BoundedContact box108451 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion108451 : ∀x,offsetBox108451.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate108451 certificate108451_valid transform108451
    padded_margins108451 enclosure108451 small_coefficients108451 bounded_contact108451

end SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
