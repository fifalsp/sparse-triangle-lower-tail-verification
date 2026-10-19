import SparseLowerTail.Section02.CutDistance

/-! Relabeling invariance and the pseudometric identities for the genuine cut distance. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section02

def BijectiveRelabeling.symm (φ : BijectiveRelabeling) : BijectiveRelabeling :=
  ⟨φ.equiv.symm,φ.preserving.symm φ.equiv⟩

def BijectiveRelabeling.comp (φ ψ : BijectiveRelabeling) : BijectiveRelabeling :=
  ⟨ψ.equiv.trans φ.equiv,φ.preserving.comp ψ.preserving⟩

def pullbackKernel (K : ℝ × ℝ → ℝ) (φ : BijectiveRelabeling) : ℝ × ℝ → ℝ :=
  fun p => K (φ.equiv p.1,φ.equiv p.2)

private theorem rectangle_values_nonempty (K : ℝ × ℝ → ℝ) :
    {v | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧ |rectangleIntegral K S T|=v}.Nonempty :=
  ⟨0,∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp [rectangleIntegral]⟩

theorem rectangleIntegral_pullback (K : ℝ × ℝ → ℝ) (φ : BijectiveRelabeling)
    (S T : Set ℝ) :
    rectangleIntegral (pullbackKernel K φ) S T =
      rectangleIntegral K (φ.equiv '' S) (φ.equiv '' T) := by
  have hp := φ.preserving.prod φ.preserving
  have hi : (φ.equiv.prodCongr φ.equiv) '' (S ×ˢ T) =
      (φ.equiv '' S) ×ˢ (φ.equiv '' T) := by
    ext p
    simp only [mem_image,mem_prod]
    constructor
    · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,h⟩
      exact ⟨⟨x,hx,congrArg Prod.fst h⟩,⟨y,hy,congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨x,hx,hxx⟩,⟨y,hy,hyy⟩⟩
      exact ⟨(x,y),⟨hx,hy⟩,Prod.ext hxx hyy⟩
  have he := hp.setIntegral_image_emb (φ.equiv.prodCongr φ.equiv).measurableEmbedding K (S ×ˢ T)
  change (∫ p in S ×ˢ T,K (φ.equiv.prodCongr φ.equiv p) ∂squareMeasure) = _
  change (∫ p in S ×ˢ T,K (Prod.map φ.equiv φ.equiv p) ∂(unitMeasure.prod unitMeasure)) = _
  rw [← he]
  change (∫ p in (φ.equiv.prodCongr φ.equiv) '' (S ×ˢ T),K p ∂squareMeasure) = _
  rw [hi]
  rfl

theorem cutNorm_pullback_le {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    (φ : BijectiveRelabeling) : cutNorm (pullbackKernel K φ) ≤ cutNorm K := by
  apply csSup_le (rectangle_values_nonempty _)
  rintro v ⟨S,T,hS,hT,rfl⟩
  rw [rectangleIntegral_pullback]
  exact abs_rectangleIntegral_le_cutNorm hK
    (φ.equiv.measurableSet_image.mpr hS) (φ.equiv.measurableSet_image.mpr hT)

theorem integrable_pullbackKernel {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    (φ : BijectiveRelabeling) : Integrable (pullbackKernel K φ) squareMeasure := by
  have hp := φ.preserving.prod φ.preserving
  exact (hp.integrable_comp_emb (φ.equiv.prodCongr φ.equiv).measurableEmbedding).mpr hK

@[simp] theorem cutNorm_pullback {K : ℝ × ℝ → ℝ} (hK : Integrable K squareMeasure)
    (φ : BijectiveRelabeling) : cutNorm (pullbackKernel K φ) = cutNorm K := by
  apply le_antisymm (cutNorm_pullback_le hK φ)
  have h := cutNorm_pullback_le (integrable_pullbackKernel hK φ) φ.symm
  have he : pullbackKernel (pullbackKernel K φ) φ.symm = K := by
    funext p
    change K (φ.equiv (φ.equiv.symm p.1),φ.equiv (φ.equiv.symm p.2)) = K p
    simp
  rw [he] at h
  exact h

@[simp] theorem cutNorm_neg (K : ℝ × ℝ → ℝ) :
    cutNorm (fun p => -K p) = cutNorm K := by
  unfold cutNorm
  congr 1
  ext v
  simp [rectangleIntegral,integral_neg,abs_neg]

theorem cutNorm_sub_comm (K L : ℝ × ℝ → ℝ) :
    cutNorm (fun p => K p-L p)= cutNorm (fun p => L p-K p) := by
  have h : (fun p => K p-L p) = (fun p => -(L p-K p)) := by funext p; ring
  rw [h,cutNorm_neg]

theorem cutNorm_relabel_swap (U W : Graphon) (φ : BijectiveRelabeling) :
    cutNorm (fun p => relabel U φ.toRelabeling p-W p) =
      cutNorm (fun p => relabel W φ.symm.toRelabeling p-U p) := by
  let K := fun p => relabel U φ.toRelabeling p-W p
  have hi : Integrable K squareMeasure := (graphon_integrable _).sub (graphon_integrable _)
  have he : pullbackKernel K φ.symm =
      (fun p => U p-relabel W φ.symm.toRelabeling p) := by
    funext p
    change U (φ.equiv (φ.equiv.symm p.1),φ.equiv (φ.equiv.symm p.2)) -
      W (φ.equiv.symm p.1,φ.equiv.symm p.2) = _
    simp [relabel,BijectiveRelabeling.toRelabeling,BijectiveRelabeling.symm]
  calc
    _ = cutNorm (pullbackKernel K φ.symm) := (cutNorm_pullback hi φ.symm).symm
    _ = _ := by rw [he,cutNorm_sub_comm]

theorem cutDistance_symm (U W : Graphon) : cutDistance U W=cutDistance W U := by
  have hle : ∀ U W : Graphon,cutDistance W U ≤ cutDistance U W := by
    intro U W
    apply le_csInf
      (show {d | ∃ φ : BijectiveRelabeling,
        cutNorm (fun p => relabel U φ.toRelabeling p-W p)=d}.Nonempty from
        ⟨_,BijectiveRelabeling.identity,rfl⟩)
    rintro d ⟨φ,rfl⟩
    rw [cutNorm_relabel_swap]
    exact cutDistance_le_relabel _ _ _
  exact le_antisymm (hle W U) (hle U W)

@[simp] theorem cutDistance_self (U : Graphon) : cutDistance U U=0 := by
  apply le_antisymm _ (cutDistance_nonneg U U)
  have h := cutDistance_le_relabel U U BijectiveRelabeling.identity
  simpa [BijectiveRelabeling.identity,BijectiveRelabeling.toRelabeling,relabel] using h

theorem cutDistance_triangle (U W Z : Graphon) :
    cutDistance U Z ≤ cutDistance U W+cutDistance W Z := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨φ,hφ⟩ := exists_relabel_cutNorm_lt U W (half_pos hε)
  obtain ⟨ψ,hψ⟩ := exists_relabel_cutNorm_lt W Z (half_pos hε)
  let K := fun p => relabel U φ.toRelabeling p-W p
  let L := fun p => relabel W ψ.toRelabeling p-Z p
  have hK : Integrable K squareMeasure := (graphon_integrable _).sub (graphon_integrable _)
  have hL : Integrable L squareMeasure := (graphon_integrable _).sub (graphon_integrable _)
  have he : (fun p => relabel U (φ.comp ψ).toRelabeling p-Z p) =
      (fun p => pullbackKernel K ψ p+L p) := by
    funext p
    change U (φ.equiv (ψ.equiv p.1),φ.equiv (ψ.equiv p.2))-Z p =
      (U (φ.equiv (ψ.equiv p.1),φ.equiv (ψ.equiv p.2))-
        W (ψ.equiv p.1,ψ.equiv p.2))+(W (ψ.equiv p.1,ψ.equiv p.2)-Z p)
    ring
  have h := cutDistance_le_relabel U Z (φ.comp ψ)
  rw [he] at h
  have hb := cutNorm_add_le (integrable_pullbackKernel hK ψ) hL
  rw [cutNorm_pullback hK ψ] at hb
  change cutNorm K < cutDistance U W+ε/2 at hφ
  change cutNorm L < cutDistance W Z+ε/2 at hψ
  linarith

/-- Almost-everywhere changes do not affect the rectangle cut norm. -/
theorem cutNorm_congr_ae {K L : ℝ × ℝ → ℝ} (h : K =ᵐ[squareMeasure] L) :
    cutNorm K=cutNorm L := by
  unfold cutNorm
  congr 1
  ext v
  have he : ∀ S T : Set ℝ,rectangleIntegral K S T=rectangleIntegral L S T :=
    fun S T => integral_congr_ae (ae_restrict_of_ae h)
  simp only [he]

theorem cutDistance_eq_zero_of_ae {U W : Graphon} (h : U.toFun =ᵐ[squareMeasure] W.toFun) :
    cutDistance U W=0 := by
  apply le_antisymm _ (cutDistance_nonneg U W)
  have hb := cutDistance_le_relabel U W BijectiveRelabeling.identity
  have he : (fun p => relabel U BijectiveRelabeling.identity.toRelabeling p-W p)
      =ᵐ[squareMeasure] (fun _ => 0) := by
    filter_upwards [h] with p hp
    simpa [relabel,BijectiveRelabeling.identity,BijectiveRelabeling.toRelabeling] using sub_eq_zero.mpr hp
  rw [cutNorm_congr_ae he,cutNorm_zero] at hb
  exact hb

/-- Classical density of invertible measure-preserving transformations in the pullback
of an integrable kernel, in L¹. This is only a measure-space approximation statement;
it contains no graphon optimization or entropy assertion. -/
def ClassicalPullbackApproximation : Prop :=
  ∀ K : ℝ × ℝ → ℝ, Integrable K squareMeasure → ∀ φ : Relabeling,
    ∀ ε : ℝ, 0<ε → ∃ ψ : BijectiveRelabeling,
      (∫ p,|K (ψ.equiv p.1,ψ.equiv p.2)-K (φ p.1,φ p.2)| ∂squareMeasure)<ε

theorem cutDistance_relabel_zero (hclass : ClassicalPullbackApproximation)
    (U : Graphon) (φ : Relabeling) : cutDistance U (relabel U φ)=0 := by
  apply le_antisymm _ (cutDistance_nonneg _ _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ψ,hψ⟩ := hclass U.toFun (graphon_integrable U) φ ε hε
  have hb := cutDistance_le_relabel U (relabel U φ) ψ
  have hl := cutNorm_le_l1 ((graphon_integrable (relabel U ψ.toRelabeling)).sub
    (graphon_integrable (relabel U φ)))
  simp only [Pi.sub_apply] at hl
  change (∫ p,|relabel U ψ.toRelabeling p-relabel U φ p| ∂squareMeasure)<ε at hψ
  simpa only [zero_add] using hb.trans (hl.trans hψ.le)

end SparseLowerTail.Section02
