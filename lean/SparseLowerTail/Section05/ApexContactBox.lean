import SparseLowerTail.Section05.ApexRefinedPrimitives
import SparseLowerTail.Section05.ApexFanLocal
import SparseLowerTail.Section05.LogBoxSubdivision

/-! Rational box-to-contact tests for the apex subdivision replay.
A proposed local leaf is accepted only if every point lies inside one of the
already proved full-radius contact neighborhoods. -/
namespace SparseLowerTail.Section05
open Numerics Certificate CoverGeometry

def apexContactBounds (mixed : Bool) : Fin 3 → RationalInterval :=
  if mixed then ![apexRefinedPrimitiveBounds 0,apexRefinedPrimitiveBounds 1,
    apexRefinedPrimitiveBounds 1] else fun _ => apexRefinedPrimitiveBounds 0

theorem apexContactBounds_contains (mixed : Bool) (j : Fin 3) :
    (apexContactBounds mixed j).contains (apexFanContact mixed j) := by
  cases mixed
  · exact apexRefinedPrimitiveBounds_contains 0
  · fin_cases j
    · exact apexRefinedPrimitiveBounds_contains 0
    · exact apexRefinedPrimitiveBounds_contains 1
    · exact apexRefinedPrimitiveBounds_contains 1

def LogBox.InApexContact (B : LogBox) (i : Fin 6) (mixed : Bool) : Prop :=
  ∀j,(apexContactBounds mixed j).upper-apexFanLocalRadius i mixed≤B.lower j ∧
    B.upper j≤(apexContactBounds mixed j).lower+apexFanLocalRadius i mixed

instance (B : LogBox) (i : Fin 6) (mixed : Bool) : Decidable (B.InApexContact i mixed) :=
  inferInstanceAs (Decidable (∀j,(apexContactBounds mixed j).upper-apexFanLocalRadius i mixed≤B.lower j ∧
    B.upper j≤(apexContactBounds mixed j).lower+apexFanLocalRadius i mixed))

theorem LogBox.mem_apex_contact {B : LogBox} {i : Fin 6} {mixed : Bool}
    (hB : B.InApexContact i mixed) {q : EdgeTriple} (hq : q∈B.region) :
    edgeCoordinate q∈familyCube (apexFanContact mixed) (apexFanLocalRadius i mixed : ℝ) := by
  intro j
  have hp := apexContactBounds_contains mixed j
  have hl : ((apexContactBounds mixed j).upper : ℝ)-(apexFanLocalRadius i mixed : ℝ)≤(B.lower j : ℝ) := by
    exact_mod_cast (hB j).1
  have hu : (B.upper j : ℝ)≤((apexContactBounds mixed j).lower : ℝ)+(apexFanLocalRadius i mixed : ℝ) := by
    exact_mod_cast (hB j).2
  have hqj := hq j
  apply abs_le.mpr
  constructor <;> linarith [hp.1,hp.2]

theorem LogBox.apex_contact_nonneg_zero_iff {B : LogBox} {i : Fin 6} {mixed : Bool}
    (hB : B.InApexContact i mixed) {q : EdgeTriple} (hq : q∈B.region) :
    0≤apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) (edgeCoordinate q) ∧
    (apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) (edgeCoordinate q)=0 ↔
      edgeCoordinate q=apexFanContact mixed) :=
  apexFan_local_nonneg_zero_iff i mixed (B.mem_apex_contact hB hq)

end SparseLowerTail.Section05
