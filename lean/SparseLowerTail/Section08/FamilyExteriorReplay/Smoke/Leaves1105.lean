import SparseLowerTail.Section08.FamilyCompactReplay
import SparseLowerTail.Section08.FamilyExteriorReplay.Smoke.Parameter0007

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def domain17695 : ReplayBox 4 := ⟨![(39/10 : ℚ),(513/128 : ℚ),(129/32 : ℚ),(129/32 : ℚ)],![(251/64 : ℚ),(129/32 : ℚ),(261/64 : ℚ),(261/64 : ℚ)]⟩
theorem conclusion17695 (hABB : FamilyABBLocal) : ∀x,domain17695.Contains x → familyCompactProperty x :=
  parameter7.compact_property_of_contact hABB parameter7_valid false (by decide +kernel)

end SparseLowerTail.Section08.FamilyExteriorReplay.Smoke
