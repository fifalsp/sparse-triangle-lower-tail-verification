import SparseLowerTail.Section03.KS23Inputs

/-! The paper's triangle decorrelation lemma, relative only to the cited generic KS23 inputs. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

/-- Enlarge the surviving hyperedge count in KS23's Cauchy-Schwarz bound and use the energy budget. -/
theorem hypergraph_error_of_ks_energy (hCS : KS23ConditionalErrorBound)
    {ι : Type} [Fintype ι] [DecidableEq ι] (H : Finset (Finset ι))
    (hH : ∀ A∈H, A.card=3) {p η β : ℝ} (hp : p∈Ioo (0:ℝ) 1)
    (hη : η∈Icc (0:ℝ) 1) (hβ : 0≤β) (W : Finset ι)
    (hbudget : ksConditionalEnergy H (hypergraphLowerLaw H 3 p η) W 3 p≤β^2*H.card/2) :
    hypergraphConditionalError H (hypergraphLowerLaw H 3 p η) W≤β*p^3*H.card := by
  have hE := ksConditionalEnergy_nonneg H (hypergraphLowerLaw H 3 p η)
    (hypergraphLowerLaw_nonneg H 3 ⟨hp.1.le,hp.2.le⟩ η) W 3 hp.1.le
  have hrem : ((unrevealedHyperedges H W).card:ℝ)≤H.card := by
    exact_mod_cast Finset.card_filter_le H (fun A => Disjoint A W)
  have hcs := hCS ι H 3 (by norm_num) hH p η hp hη W
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hcs
  have hroot : Real.sqrt (2*(unrevealedHyperedges H W).card)≤Real.sqrt (2*(H.card:ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hroot
      (Real.sqrt_nonneg (ksConditionalEnergy H (hypergraphLowerLaw H 3 p η) W 3 p))) (pow_nonneg hp.1.le 3)
  exact decorrelation_error_of_energy hβ (Nat.cast_nonneg _) hE hp.1.le hbudget (hcs.trans hh)

/-- Manuscript lem:decorrelation: all triangle-specific counts, codegrees and parameters are discharged. -/
theorem triangle_decorrelation (hSelection : KS23EnergySelection) (hCS : KS23ConditionalErrorBound)
    {α β : ℝ} (hα : α∈Ioo (0:ℝ) 1) (hβ : β∈Ioo (0:ℝ) 1) :
    ∃ L : ℝ, 4≤L ∧ ∀ n : ℕ, L≤(n:ℝ) → ∀ p : ℝ,
      L*(n:ℝ)^(-(1/(2:ℝ)))≤p → p≤1/2 → ∀ η : ℝ, η∈Ioo (0:ℝ) 1 →
      ∃ W : Finset (GraphEdgeCoordinate n), (W.card:ℝ)≤α*(n.choose 2:ℝ) ∧
        hypergraphConditionalError (coordinateTriangleHypergraph n)
          (hypergraphLowerLaw (coordinateTriangleHypergraph n) 3 p η) W≤β*p^3*(n.choose 3:ℝ) := by
  have hβpos : 0<β := hβ.1
  obtain ⟨ell,hell,V₀,hselect⟩ := hSelection 3 (by norm_num) (1/2) (by norm_num)
    α (β^2/2) 3 hα.1 (by positivity) (by norm_num)
  let L := max 4 (max (2/ell) ((V₀:ℝ)+2))
  refine ⟨L,le_max_left _ _,?_⟩
  intro n hn p hp hpmax η hη
  have hn4 : 4≤n := by exact_mod_cast ((le_max_left _ _).trans hn : (4:ℝ)≤n)
  have hnV : V₀+2≤n := by
    exact_mod_cast ((le_max_right (2/ell) ((V₀:ℝ)+2)).trans ((le_max_right 4 _).trans hn))
  have hsize : V₀≤Fintype.card (GraphEdgeCoordinate n) := by
    rw [graphEdgeCoordinate_card]
    have hh := triangle_vertex_budget V₀ n hnV
    unfold triangleVertexCount at hh
    exact_mod_cast hh
  have hLell : 2/ell≤L := (le_max_left _ _).trans (le_max_right _ _)
  rw [sparse_half_power_identity] at hp
  have hpell : (2/ell)/Real.sqrt n≤p :=
    (div_le_div_of_nonneg_right hLell (Real.sqrt_nonneg _)).trans hp
  have hpn : p∈Ioo (0:ℝ) 1 := by
    have hroot : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0<n))
    have hpos := lt_of_lt_of_le (div_pos (div_pos (by norm_num) hell) hroot) hpell
    exact ⟨hpos,by linarith⟩
  obtain ⟨W,hW,hE⟩ := hselect (GraphEdgeCoordinate n) (coordinateTriangleHypergraph n)
    (fun _ hA => coordinateTriangleHypergraph_uniform hA) hsize p η hpn hpmax
    ⟨hη.1.le,hη.2.le⟩ (coordinateTriangleHypergraph_codegree_condition n hn4 hell hpell)
  refine ⟨W,?_,?_⟩
  · simpa only [graphEdgeCoordinate_card] using hW
  · have hh := hypergraph_error_of_ks_energy hCS (coordinateTriangleHypergraph n)
      (fun _ hA => coordinateTriangleHypergraph_uniform hA) hpn ⟨hη.1.le,hη.2.le⟩ hβ.1.le W
      (by simpa only [div_mul_eq_mul_div] using hE)
    simpa only [coordinateTriangleHypergraph_card] using hh

end SparseLowerTail.Section03
