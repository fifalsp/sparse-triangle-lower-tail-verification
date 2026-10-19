import SparseLowerTail.Section08.FamilyCompactReplay
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0006

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def domain2808 : ReplayBox 4 := ⟨![(39/10 : ℚ),(261/64 : ℚ),(9/128 : ℚ),(3/32 : ℚ)],![(319/80 : ℚ),(33/8 : ℚ),(3/32 : ℚ),(9/64 : ℚ)]⟩
theorem conclusion2808 (hABB : FamilyABBLocal) : ∀x,domain2808.Contains x → familyCompactProperty x :=
  parameter6.compact_property_of_contact hABB parameter6_valid true (by decide +kernel)

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
