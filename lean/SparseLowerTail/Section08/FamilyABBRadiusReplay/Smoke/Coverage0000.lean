import SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke.Leaves0000
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Coverage0000

/-! Generated proposals; every numerical assertion is checked by Lean. -/
namespace SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate SparseLowerTail.Section04
open SparseLowerTail.Certificate.HessianRadiusTransfer
open SparseLowerTail.Section08.FamilyABBReplay.Smoke
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Coverage0000
abbrev initialBox := SparseLowerTail.Section08.FamilyABBReplay.Smoke.Coverage0000.initialBox
abbrev leafTable := SparseLowerTail.Section08.FamilyABBReplay.Smoke.Coverage0000.leafTable
abbrev subdivision := SparseLowerTail.Section08.FamilyABBReplay.Smoke.Coverage0000.subdivision
theorem leaf_proofs : leafTable.All (ReplayBoxProperty RadiusABBOffsetProperty) := ⟨⟨⟨⟨⟨radius_conclusion0,radius_conclusion16⟩,⟨radius_conclusion8,True.intro⟩⟩,⟨⟨radius_conclusion4,True.intro⟩,⟨radius_conclusion12,True.intro⟩⟩⟩,⟨⟨⟨radius_conclusion2,radius_conclusion18⟩,⟨radius_conclusion10,True.intro⟩⟩,⟨⟨radius_conclusion6,True.intro⟩,⟨radius_conclusion14,True.intro⟩⟩⟩⟩,⟨⟨⟨⟨radius_conclusion1,radius_conclusion17⟩,⟨radius_conclusion9,True.intro⟩⟩,⟨⟨radius_conclusion5,True.intro⟩,⟨radius_conclusion13,True.intro⟩⟩⟩,⟨⟨⟨radius_conclusion3,radius_conclusion19⟩,⟨radius_conclusion11,True.intro⟩⟩,⟨⟨radius_conclusion7,True.intro⟩,⟨radius_conclusion15,True.intro⟩⟩⟩⟩⟩
theorem covered : ∀x,initialBox.Contains x → RadiusABBOffsetProperty x :=
  subdivision.sound_table leaf_proofs SparseLowerTail.Section08.FamilyABBReplay.Smoke.Coverage0000.valid
end Coverage0000

end SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
