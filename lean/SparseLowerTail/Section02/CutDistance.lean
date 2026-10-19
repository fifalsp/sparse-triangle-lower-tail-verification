import SparseLowerTail.Section02.Relabeling

/-! The relabeling-infimum cut distance and selection of convergent representatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- A genuine measurable bijection preserving the unit-interval probability measure. -/
structure BijectiveRelabeling where
  equiv : ℝ ≃ᵐ ℝ
  preserving : MeasurePreserving equiv unitMeasure unitMeasure

def BijectiveRelabeling.toRelabeling (φ : BijectiveRelabeling) : Relabeling :=
  ⟨φ.equiv,φ.preserving⟩

def BijectiveRelabeling.identity : BijectiveRelabeling :=
  ⟨MeasurableEquiv.refl ℝ,MeasurePreserving.id unitMeasure⟩

/-- Cut distance defined by the actual infimum over measure-preserving measurable bijections.
No metric, symmetry, or compactness assertion is bundled into this definition. -/
def cutDistance (U W : Graphon) : ℝ :=
  sInf {d | ∃ φ : BijectiveRelabeling,
    cutNorm (fun p => relabel U φ.toRelabeling p-W p)=d}

private theorem relabeled_distances_nonempty (U W : Graphon) :
    {d | ∃ φ : BijectiveRelabeling,cutNorm (fun p => relabel U φ.toRelabeling p-W p)=d}.Nonempty :=
  ⟨_,BijectiveRelabeling.identity,rfl⟩

private theorem relabeled_distances_bddBelow (U W : Graphon) :
    BddBelow {d | ∃ φ : BijectiveRelabeling,cutNorm (fun p => relabel U φ.toRelabeling p-W p)=d} := by
  refine ⟨0,?_⟩
  rintro d ⟨φ,rfl⟩
  exact cutNorm_nonneg ((graphon_integrable _).sub (graphon_integrable W))

theorem cutDistance_nonneg (U W : Graphon) : 0 ≤ cutDistance U W := by
  apply le_csInf (relabeled_distances_nonempty U W)
  rintro d ⟨φ,rfl⟩
  exact cutNorm_nonneg ((graphon_integrable _).sub (graphon_integrable W))

theorem cutDistance_le_relabel (U W : Graphon) (φ : BijectiveRelabeling) :
    cutDistance U W ≤ cutNorm (fun p => relabel U φ.toRelabeling p-W p) :=
  csInf_le (relabeled_distances_bddBelow U W) ⟨φ,rfl⟩

/-- Approximate the defining infimum by a genuine bijective relabeling. -/
theorem exists_relabel_cutNorm_lt (U W : Graphon) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : BijectiveRelabeling,
      cutNorm (fun p => relabel U φ.toRelabeling p-W p)<cutDistance U W+ε := by
  obtain ⟨d,⟨φ,rfl⟩,hd⟩ := exists_lt_of_csInf_lt (relabeled_distances_nonempty U W)
    (show cutDistance U W<cutDistance U W+ε by linarith)
  exact ⟨φ,hd⟩

/-- Cut-distance convergence has representatives converging in actual cut norm. -/
theorem exists_relabel_cutConverges {U : ℕ → Graphon} {W : Graphon}
    (h : Tendsto (fun n => cutDistance (U n) W) atTop (𝓝 0)) :
    ∃ φ : ℕ → BijectiveRelabeling,
      CutConverges (fun n => relabel (U n) (φ n).toRelabeling) W := by
  have hex : ∀ n : ℕ, ∃ φ : BijectiveRelabeling,
      cutNorm (fun p => relabel (U n) φ.toRelabeling p-W p)<cutDistance (U n) W+1/((n:ℝ)+1) :=
    fun n => exists_relabel_cutNorm_lt _ _ (by positivity)
  choose φ hφ using hex
  refine ⟨φ,?_⟩
  apply squeeze_zero
    (fun n => cutNorm_nonneg ((graphon_integrable _).sub (graphon_integrable W)))
    (fun n => (hφ n).le)
  simpa only [add_zero] using h.add tendsto_one_div_add_atTop_nhds_zero_nat

end SparseLowerTail.Section02
