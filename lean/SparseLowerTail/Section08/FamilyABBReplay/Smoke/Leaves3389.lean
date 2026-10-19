import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Parameter0002
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Endpoints0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def offsetBox108451 : ReplayBox 4 := ⟨![(44/5 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(19/2 : ℚ),(1/10 : ℚ),(1/10 : ℚ),(1/10 : ℚ)]⟩
def box108451 : FamilyBoxCertificate := ⟨parameter2,coefficients2,![exp51,exp0,exp0],![exp54,exp15,exp15]⟩
theorem box108451_valid : box108451.Valid := by
  refine ⟨parameter2_valid,coefficients2_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp51_valid
    · exact exp0_valid
    · exact exp0_valid
  · intro j; fin_cases j
    · exact exp54_valid
    · exact exp15_valid
    · exact exp15_valid
def certificate108451 : FamilyScaledBoxCertificate := ⟨box108451,![![exp51,exp49,exp49],![exp49,exp0,exp0],![exp49,exp0,exp0]],![![exp54,exp50,exp50],![exp50,exp15,exp15],![exp50,exp15,exp15]]⟩
theorem certificate108451_valid : certificate108451.Valid := by
  refine ⟨box108451_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp49_valid,exp50_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp49_valid,exp50_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp49_valid,exp50_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp0_valid,exp15_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp49_valid,exp50_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp0_valid,exp15_valid,by decide +kernel,by decide +kernel⟩
def transform108451 : FamilyRationalMatrix := ![![(1468559/1000000 : ℚ),(-14687/500000 : ℚ),(-15789/500000 : ℚ)],![(0/1 : ℚ),(267229/31250 : ℚ),(309661/500000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(4286863/500000 : ℚ)]]
theorem margins108451 : FamilyIntervalPositive (familyIntervalCongruence certificate108451.hessianIntervals transform108451) := by decide +kernel
theorem enclosure108451 : box108451.EnclosesABBOffsets offsetBox108451 := by decide +kernel
theorem conclusion108451 : ∀x,offsetBox108451.Contains x → familyABBOffsetProperty x :=
  certificate108451.abb_offset_property certificate108451_valid transform108451 margins108451 enclosure108451

end SparseLowerTail.Section08.FamilyABBReplay.Smoke
