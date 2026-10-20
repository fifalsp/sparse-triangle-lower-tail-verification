import SparseLowerTail.Section02.KernelCutDistance
import SparseLowerTail.Section02.WeightedCut

/-! The own-paper passage from classical compactness to bijective representatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

theorem exists_bijective_cut_approximation (hclass : ClassicalPullbackApproximation)
    (U : Graphon) (φ : Relabeling) {ε : ℝ} (hε : 0<ε) :
    ∃ ψ : BijectiveRelabeling,
      cutNorm (fun p => relabel U ψ.toRelabeling p-relabel U φ p)<ε := by
  obtain ⟨ψ,hψ⟩ := hclass U.toFun (graphon_integrable U) φ ε hε
  refine ⟨ψ,?_⟩
  have hl := cutNorm_le_l1 ((graphon_integrable (relabel U ψ.toRelabeling)).sub
    (graphon_integrable (relabel U φ)))
  exact hl.trans_lt hψ

/-- Every sequence has genuine bijections giving cut-norm convergence along a subsequence. -/
theorem exists_bijective_cut_subsequence (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (U : ℕ → Graphon) :
    ∃ W : Graphon,∃ σ : ℕ → ℕ,∃ ψ : ℕ → BijectiveRelabeling,
      StrictMono σ ∧ CutConverges (fun n => relabel (U (σ n)) (ψ n).toRelabeling) W := by
  obtain ⟨W,σ,φ,hσ,hconv⟩ := hcompact U
  have hex : ∀ n : ℕ,∃ ψ : BijectiveRelabeling,
      cutNorm (fun p => relabel (U (σ n)) ψ.toRelabeling p-relabel (U (σ n)) (φ n) p)<
        1/((n:ℝ)+1) :=
    fun n => exists_bijective_cut_approximation hpull (U (σ n)) (φ n) (by positivity)
  choose ψ hψ using hex
  refine ⟨W,σ,ψ,hσ,?_⟩
  have ht : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)+
      cutNorm (fun p => relabel (U (σ n)) (φ n) p-W p)) atTop (𝓝 0) := by
    simpa only [zero_add] using tendsto_one_div_add_atTop_nhds_zero_nat.add hconv
  apply squeeze_zero
    (fun n => cutNorm_nonneg ((graphon_integrable _).sub (graphon_integrable W)))
    (fun n => ?_) ht
  let D:=fun p => relabel (U (σ n)) (ψ n).toRelabeling p-relabel (U (σ n)) (φ n) p
  let E:=fun p => relabel (U (σ n)) (φ n) p-W p
  have hD : Integrable D squareMeasure := (graphon_integrable _).sub (graphon_integrable _)
  have hE : Integrable E squareMeasure := (graphon_integrable _).sub (graphon_integrable _)
  have he : (fun p => relabel (U (σ n)) (ψ n).toRelabeling p-W p)=
      (fun p => D p+E p) := by funext p;dsimp [D,E];ring
  change cutNorm (fun p => relabel (U (σ n)) (ψ n).toRelabeling p-W p)≤_
  rw [he]
  exact (cutNorm_add_le hD hE).trans (add_le_add_right (hψ n).le _)

/-- The two literal counting bounds in part (b). -/
theorem cut_counting_bounds (hcount : ClassicalTriangleCounting) (U W : Graphon) :
    |edgeDensity U-edgeDensity W|≤cutNorm (fun p => U p-W p) ∧
    |triangle U-triangle W|≤3*cutNorm (fun p => U p-W p) := by
  refine ⟨?_,hcount U W⟩
  have h := abs_rectangleIntegral_le_cutNorm ((graphon_integrable U).sub (graphon_integrable W))
    MeasurableSet.univ MeasurableSet.univ
  simp only [rectangleIntegral,univ_prod_univ,setIntegral_univ] at h
  change |∫ p,(U p-W p) ∂squareMeasure|≤_ at h
  rw [integral_sub (graphon_integrable U) (graphon_integrable W)] at h
  exact h

end SparseLowerTail.Section02
