import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Leaves0000
import SparseLowerTail.Section08.FamilyHessianRadiusTransfer

/-! Generated proposals; every numerical assertion is checked by Lean. -/
namespace SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
open SparseLowerTail.Numerics SparseLowerTail.Certificate SparseLowerTail.Section04
open SparseLowerTail.Certificate.HessianRadiusTransfer
open SparseLowerTail.Section08.FamilyABBReplay.Smoke
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem padded_margins0 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate0.hessianIntervals) transform0) := by
  decide +kernel

theorem small_coefficients0 : ∀j,SmallCoefficient (box0.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact0 : BoundedContact box0 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion0 : ∀x,offsetBox0.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate0 certificate0_valid transform0
    padded_margins0 enclosure0 small_coefficients0 bounded_contact0

theorem padded_margins1 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate1.hessianIntervals) transform1) := by
  decide +kernel

theorem small_coefficients1 : ∀j,SmallCoefficient (box1.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact1 : BoundedContact box1 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion1 : ∀x,offsetBox1.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate1 certificate1_valid transform1
    padded_margins1 enclosure1 small_coefficients1 bounded_contact1

theorem padded_margins2 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate2.hessianIntervals) transform2) := by
  decide +kernel

theorem small_coefficients2 : ∀j,SmallCoefficient (box2.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact2 : BoundedContact box2 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion2 : ∀x,offsetBox2.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate2 certificate2_valid transform2
    padded_margins2 enclosure2 small_coefficients2 bounded_contact2

theorem padded_margins3 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate3.hessianIntervals) transform3) := by
  decide +kernel

theorem small_coefficients3 : ∀j,SmallCoefficient (box3.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact3 : BoundedContact box3 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion3 : ∀x,offsetBox3.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate3 certificate3_valid transform3
    padded_margins3 enclosure3 small_coefficients3 bounded_contact3

theorem padded_margins4 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate4.hessianIntervals) transform4) := by
  decide +kernel

theorem small_coefficients4 : ∀j,SmallCoefficient (box4.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact4 : BoundedContact box4 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion4 : ∀x,offsetBox4.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate4 certificate4_valid transform4
    padded_margins4 enclosure4 small_coefficients4 bounded_contact4

theorem padded_margins5 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate5.hessianIntervals) transform5) := by
  decide +kernel

theorem small_coefficients5 : ∀j,SmallCoefficient (box5.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact5 : BoundedContact box5 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion5 : ∀x,offsetBox5.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate5 certificate5_valid transform5
    padded_margins5 enclosure5 small_coefficients5 bounded_contact5

theorem padded_margins6 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate6.hessianIntervals) transform6) := by
  decide +kernel

theorem small_coefficients6 : ∀j,SmallCoefficient (box6.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact6 : BoundedContact box6 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion6 : ∀x,offsetBox6.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate6 certificate6_valid transform6
    padded_margins6 enclosure6 small_coefficients6 bounded_contact6

theorem padded_margins7 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate7.hessianIntervals) transform7) := by
  decide +kernel

theorem small_coefficients7 : ∀j,SmallCoefficient (box7.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact7 : BoundedContact box7 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion7 : ∀x,offsetBox7.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate7 certificate7_valid transform7
    padded_margins7 enclosure7 small_coefficients7 bounded_contact7

theorem padded_margins8 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate8.hessianIntervals) transform8) := by
  decide +kernel

theorem small_coefficients8 : ∀j,SmallCoefficient (box8.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact8 : BoundedContact box8 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion8 : ∀x,offsetBox8.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate8 certificate8_valid transform8
    padded_margins8 enclosure8 small_coefficients8 bounded_contact8

theorem padded_margins9 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate9.hessianIntervals) transform9) := by
  decide +kernel

theorem small_coefficients9 : ∀j,SmallCoefficient (box9.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact9 : BoundedContact box9 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion9 : ∀x,offsetBox9.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate9 certificate9_valid transform9
    padded_margins9 enclosure9 small_coefficients9 bounded_contact9

theorem padded_margins10 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate10.hessianIntervals) transform10) := by
  decide +kernel

theorem small_coefficients10 : ∀j,SmallCoefficient (box10.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact10 : BoundedContact box10 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion10 : ∀x,offsetBox10.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate10 certificate10_valid transform10
    padded_margins10 enclosure10 small_coefficients10 bounded_contact10

theorem padded_margins11 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate11.hessianIntervals) transform11) := by
  decide +kernel

theorem small_coefficients11 : ∀j,SmallCoefficient (box11.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact11 : BoundedContact box11 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion11 : ∀x,offsetBox11.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate11 certificate11_valid transform11
    padded_margins11 enclosure11 small_coefficients11 bounded_contact11

theorem padded_margins12 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate12.hessianIntervals) transform12) := by
  decide +kernel

theorem small_coefficients12 : ∀j,SmallCoefficient (box12.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact12 : BoundedContact box12 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion12 : ∀x,offsetBox12.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate12 certificate12_valid transform12
    padded_margins12 enclosure12 small_coefficients12 bounded_contact12

theorem padded_margins13 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate13.hessianIntervals) transform13) := by
  decide +kernel

theorem small_coefficients13 : ∀j,SmallCoefficient (box13.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact13 : BoundedContact box13 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion13 : ∀x,offsetBox13.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate13 certificate13_valid transform13
    padded_margins13 enclosure13 small_coefficients13 bounded_contact13

theorem padded_margins14 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate14.hessianIntervals) transform14) := by
  decide +kernel

theorem small_coefficients14 : ∀j,SmallCoefficient (box14.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact14 : BoundedContact box14 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion14 : ∀x,offsetBox14.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate14 certificate14_valid transform14
    padded_margins14 enclosure14 small_coefficients14 bounded_contact14

theorem padded_margins15 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate15.hessianIntervals) transform15) := by
  decide +kernel

theorem small_coefficients15 : ∀j,SmallCoefficient (box15.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact15 : BoundedContact box15 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion15 : ∀x,offsetBox15.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate15 certificate15_valid transform15
    padded_margins15 enclosure15 small_coefficients15 bounded_contact15

theorem padded_margins16 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate16.hessianIntervals) transform16) := by
  decide +kernel

theorem small_coefficients16 : ∀j,SmallCoefficient (box16.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact16 : BoundedContact box16 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion16 : ∀x,offsetBox16.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate16 certificate16_valid transform16
    padded_margins16 enclosure16 small_coefficients16 bounded_contact16

theorem padded_margins17 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate17.hessianIntervals) transform17) := by
  decide +kernel

theorem small_coefficients17 : ∀j,SmallCoefficient (box17.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact17 : BoundedContact box17 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion17 : ∀x,offsetBox17.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate17 certificate17_valid transform17
    padded_margins17 enclosure17 small_coefficients17 bounded_contact17

theorem padded_margins18 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate18.hessianIntervals) transform18) := by
  decide +kernel

theorem small_coefficients18 : ∀j,SmallCoefficient (box18.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact18 : BoundedContact box18 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion18 : ∀x,offsetBox18.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate18 certificate18_valid transform18
    padded_margins18 enclosure18 small_coefficients18 bounded_contact18

theorem padded_margins19 : FamilyIntervalPositive
    (familyIntervalCongruence (paddedMatrix certificate19.hessianIntervals) transform19) := by
  decide +kernel

theorem small_coefficients19 : ∀j,SmallCoefficient (box19.coefficient j) := by
  intro j; fin_cases j <;> decide +kernel

theorem bounded_contact19 : BoundedContact box19 := by
  intro j; fin_cases j <;> decide +kernel

theorem radius_conclusion19 : ∀x,offsetBox19.Contains x → RadiusABBOffsetProperty x :=
  abb_radius_offset_property certificate19 certificate19_valid transform19
    padded_margins19 enclosure19 small_coefficients19 bounded_contact19

end SparseLowerTail.Section08.FamilyABBRadiusReplay.Smoke
