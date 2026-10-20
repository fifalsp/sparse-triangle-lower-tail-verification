import SparseLowerTail.Section02.CutDistanceIdentities

/-! The actual bijective cut distance for arbitrary integrable real kernels. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

/-- The paper's infimum, with no graphon range restriction on either kernel. -/
def kernelCutDistance (K L : ℝ × ℝ → ℝ) : ℝ :=
  sInf {d | ∃ φ : BijectiveRelabeling,cutNorm (fun p => pullbackKernel K φ p-L p)=d}

private theorem kernel_distances_nonempty (K L : ℝ × ℝ → ℝ) :
    {d | ∃ φ : BijectiveRelabeling,cutNorm (fun p => pullbackKernel K φ p-L p)=d}.Nonempty :=
  ⟨_,BijectiveRelabeling.identity,rfl⟩

private theorem kernel_distances_bddBelow {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) :
    BddBelow {d | ∃ φ : BijectiveRelabeling,cutNorm (fun p => pullbackKernel K φ p-L p)=d} := by
  refine ⟨0,?_⟩
  rintro d ⟨φ,rfl⟩
  exact cutNorm_nonneg ((integrable_pullbackKernel hK φ).sub hL)

theorem kernelCutDistance_nonneg {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) :
    0≤kernelCutDistance K L := by
  apply le_csInf (kernel_distances_nonempty K L)
  rintro d ⟨φ,rfl⟩
  exact cutNorm_nonneg ((integrable_pullbackKernel hK φ).sub hL)

theorem kernelCutDistance_le_pullback {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) (φ : BijectiveRelabeling) :
    kernelCutDistance K L≤cutNorm (fun p => pullbackKernel K φ p-L p) :=
  csInf_le (kernel_distances_bddBelow hK hL) ⟨φ,rfl⟩

theorem exists_pullback_kernelCutNorm_lt (K L : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ φ : BijectiveRelabeling,
      cutNorm (fun p => pullbackKernel K φ p-L p)<kernelCutDistance K L+ε := by
  obtain ⟨d,⟨φ,rfl⟩,hd⟩ := exists_lt_of_csInf_lt (kernel_distances_nonempty K L)
    (show kernelCutDistance K L<kernelCutDistance K L+ε by linarith)
  exact ⟨φ,hd⟩

theorem cutNorm_kernel_swap {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) (φ : BijectiveRelabeling) :
    cutNorm (fun p => pullbackKernel K φ p-L p)=
      cutNorm (fun p => pullbackKernel L φ.symm p-K p) := by
  let D:=fun p => pullbackKernel K φ p-L p
  have hD : Integrable D squareMeasure := (integrable_pullbackKernel hK φ).sub hL
  have he : pullbackKernel D φ.symm=(fun p => K p-pullbackKernel L φ.symm p) := by
    funext p
    change K (φ.equiv (φ.equiv.symm p.1),φ.equiv (φ.equiv.symm p.2))-
      L (φ.equiv.symm p.1,φ.equiv.symm p.2)=_
    simp [pullbackKernel,BijectiveRelabeling.symm]
  calc
    _=cutNorm (pullbackKernel D φ.symm) := (cutNorm_pullback hD φ.symm).symm
    _=_ := by rw [he,cutNorm_sub_comm]

theorem kernelCutDistance_symm {K L : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure) :
    kernelCutDistance K L=kernelCutDistance L K := by
  have hle {K L : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
      (hL : Integrable L squareMeasure) : kernelCutDistance L K≤kernelCutDistance K L := by
    apply le_csInf (kernel_distances_nonempty K L)
    rintro d ⟨φ,rfl⟩
    rw [cutNorm_kernel_swap hK hL φ]
    exact kernelCutDistance_le_pullback hL hK _
  exact le_antisymm (hle hL hK) (hle hK hL)

theorem kernelCutDistance_self {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure) :
    kernelCutDistance K K=0 := by
  apply le_antisymm _ (kernelCutDistance_nonneg hK hK)
  have h:=kernelCutDistance_le_pullback hK hK BijectiveRelabeling.identity
  simpa [pullbackKernel,BijectiveRelabeling.identity] using h

theorem kernelCutDistance_triangle {K L M : ℝ × ℝ → ℝ}
    (hK : Integrable K squareMeasure) (hL : Integrable L squareMeasure)
    (hM : Integrable M squareMeasure) :
    kernelCutDistance K M≤kernelCutDistance K L+kernelCutDistance L M := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨φ,hφ⟩ := exists_pullback_kernelCutNorm_lt K L (half_pos hε)
  obtain ⟨ψ,hψ⟩ := exists_pullback_kernelCutNorm_lt L M (half_pos hε)
  let D:=fun p => pullbackKernel K φ p-L p
  let E:=fun p => pullbackKernel L ψ p-M p
  have hD : Integrable D squareMeasure := (integrable_pullbackKernel hK φ).sub hL
  have hE : Integrable E squareMeasure := (integrable_pullbackKernel hL ψ).sub hM
  have he : (fun p => pullbackKernel K (φ.comp ψ) p-M p)=
      (fun p => pullbackKernel D ψ p+E p) := by
    funext p
    change K (φ.equiv (ψ.equiv p.1),φ.equiv (ψ.equiv p.2))-M p=
      (K (φ.equiv (ψ.equiv p.1),φ.equiv (ψ.equiv p.2))-L (ψ.equiv p.1,ψ.equiv p.2))+
        (L (ψ.equiv p.1,ψ.equiv p.2)-M p)
    ring
  have h:=kernelCutDistance_le_pullback hK hM (φ.comp ψ)
  rw [he] at h
  have hb:=cutNorm_add_le (integrable_pullbackKernel hD ψ) hE
  rw [cutNorm_pullback hD ψ] at hb
  change cutNorm D<kernelCutDistance K L+ε/2 at hφ
  change cutNorm E<kernelCutDistance L M+ε/2 at hψ
  linarith

theorem kernelCutDistance_graphon (U W : Graphon) :
    kernelCutDistance U.toFun W.toFun=cutDistance U W := rfl

/-- Pullbacks by arbitrary preserving maps have zero distance, even for signed kernels. -/
theorem kernelCutDistance_relabel_zero (hclass : ClassicalPullbackApproximation)
    {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure) (φ : Relabeling) :
    kernelCutDistance K (fun p => K (φ p.1,φ p.2))=0 := by
  have hφ : Integrable (fun p => K (φ p.1,φ p.2)) squareMeasure :=
    (φ.preserving.prod φ.preserving).integrable_comp_of_integrable hK
  apply le_antisymm _ (kernelCutDistance_nonneg hK hφ)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ψ,hψ⟩:=hclass K hK φ ε hε
  have hb:=kernelCutDistance_le_pullback hK hφ ψ
  have hl:=cutNorm_le_l1 ((integrable_pullbackKernel hK ψ).sub hφ)
  change (∫ p,|pullbackKernel K ψ p-K (φ p.1,φ p.2)| ∂squareMeasure)<ε at hψ
  simpa only [zero_add] using hb.trans (hl.trans hψ.le)

/-- Part (d) on the full integrable-kernel domain. -/
theorem kernel_cut_metric (hclass : ClassicalPullbackApproximation)
    {K L M : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    (hL : Integrable L squareMeasure) (hM : Integrable M squareMeasure) (φ : Relabeling) :
    kernelCutDistance K M=kernelCutDistance M K ∧
    kernelCutDistance K M≤kernelCutDistance K L+kernelCutDistance L M ∧
    kernelCutDistance (fun p => K (φ p.1,φ p.2)) K=0 := by
  have hφ : Integrable (fun p => K (φ p.1,φ p.2)) squareMeasure :=
    (φ.preserving.prod φ.preserving).integrable_comp_of_integrable hK
  exact ⟨kernelCutDistance_symm hK hM,kernelCutDistance_triangle hK hL hM,
    (kernelCutDistance_symm hφ hK).trans (kernelCutDistance_relabel_zero hclass hK φ)⟩

end SparseLowerTail.Section02
