import SparseLowerTail.Section05.CoverS1Expr
import SparseLowerTail.Section05.CoverConstantDigits
import SparseLowerTail.Section05.LogBoxSubdivision

/-! Reusable interval environment for the exact S1 certificate. -/
namespace SparseLowerTail.Section05
open Section04 Numerics

def s1TriangleInterval : RationalInterval :=
  ⟨9217366866/1000000000000,9217366881/1000000000000⟩
def s1OmegaInterval : RationalInterval := ⟨92312137/100000000,92312139/100000000⟩
def s1MuInterval : RationalInterval :=
  ⟨173856571583/5000000000,347713218831/10000000000⟩

theorem s1TriangleInterval_contains : s1TriangleInterval.contains criticalTriangle := by
  have h := criticalTriangle_sharp_bounds
  norm_num [s1TriangleInterval,RationalInterval.contains] at h ⊢
  exact h

theorem s1OmegaInterval_contains : s1OmegaInterval.contains criticalOmega := by
  have h := criticalOmega_checked_bounds
  norm_num [s1OmegaInterval,RationalInterval.contains] at h ⊢
  exact h

theorem s1MuInterval_contains : s1MuInterval.contains (relaxationMultiplier coverS1Vertex0) := by
  have h := coverS1_hmu_bounds (qv := ((0,0),0)) (by norm_num [logCube])
  simpa only [s1MuInterval,RationalInterval.contains,Rat.cast_div,Rat.cast_ofNat] using h

def s1BoxEnvironment (qb eb : Fin 3 → RationalInterval) : Fin 9 → RationalInterval :=
  ![qb 0,qb 1,qb 2,eb 0,eb 1,eb 2,s1TriangleInterval,s1OmegaInterval,s1MuInterval]

theorem s1BoxEnvironment_contains (qb eb : Fin 3 → RationalInterval) {q : EdgeTriple}
    (hq : ∀ i, (qb i).contains (edgeCoordinate q i))
    (he : ∀ i, (eb i).contains (Real.exp (-(edgeCoordinate q i)))) :
    ∀ i, (s1BoxEnvironment qb eb i).contains (s1Environment q i) := by
  intro i
  fin_cases i
  · exact hq 0
  · exact hq 1
  · exact hq 2
  · exact he 0
  · exact he 1
  · exact he 2
  · exact s1TriangleInterval_contains
  · exact s1OmegaInterval_contains
  · exact s1MuInterval_contains

end SparseLowerTail.Section05
