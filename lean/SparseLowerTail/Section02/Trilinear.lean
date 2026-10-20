import SparseLowerTail.Section02.TriangleL2

/-! The full trilinear identities and bounds for bounded real symmetric kernels. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section02
open TriangleIntegration

/-- The actual mixed triangle integral of three real kernels. -/
def mixedTriangle (K L M : ℝ×ℝ → ℝ) : ℝ :=
  ∫ p : (ℝ×ℝ)×ℝ, K p.1*L (p.1.2,p.2)*M (p.1.1,p.2) ∂tripleMeasure

def AEKerSymmetric (K : ℝ×ℝ → ℝ) : Prop := ∀ᵐ p ∂squareMeasure, K p.swap=K p

theorem mixedTriangle_integrable {K L M : ℝ×ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hL : BoundedObservable squareMeasure L)
    (hM : BoundedObservable squareMeasure M) :
    Integrable (fun p : (ℝ×ℝ)×ℝ => K p.1*L (p.1.2,p.2)*M (p.1.1,p.2)) tripleMeasure :=
  (((hK.comp edgeX_qmp).mul (hL.comp edgeY_qmp)).mul (hM.comp edgeZ_qmp)).integrable

/-- Cyclic symmetry uses only a.e. symmetry of the two kernels whose arguments reverse. -/
theorem mixedTriangle_cycle (K L M : ℝ×ℝ → ℝ) (hL : AEKerSymmetric L) (hM : AEKerSymmetric M) :
    mixedTriangle M K L=mixedTriangle K L M := by
  calc
    _=∫ p, K (cycle p).1*L ((cycle p).1.2,(cycle p).2)*M ((cycle p).1.1,(cycle p).2) ∂tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [edgeZ_qmp.ae hL,edgeX_qmp.ae hM] with p hp hq
      change L (p.2,p.1.1)=L (p.1.1,p.2) at hp
      change M (p.1.2,p.1.1)=M (p.1.1,p.1.2) at hq
      change M p.1*K (p.1.2,p.2)*L (p.1.1,p.2)=
        K (p.1.2,p.2)*L (p.2,p.1.1)*M (p.1.2,p.1.1)
      rw [hp,hq]
      ring
    _=_ := cycle_preserving.integral_comp cycle.measurableEmbedding
      (fun p => K p.1*L (p.1.2,p.2)*M (p.1.1,p.2))

/-- Swapping the last two kernels is induced by swapping the first two vertices. -/
theorem mixedTriangle_swap_right (K L M : ℝ×ℝ → ℝ) (hK : AEKerSymmetric K) :
    mixedTriangle K M L=mixedTriangle K L M := by
  let σ : ((ℝ×ℝ)×ℝ)≃ᵐ((ℝ×ℝ)×ℝ) := MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl ℝ)
  have hσ : MeasurePreserving σ tripleMeasure tripleMeasure :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id unitMeasure)
  calc
    _=∫ p, K (σ p).1*L ((σ p).1.2,(σ p).2)*M ((σ p).1.1,(σ p).2) ∂tripleMeasure := by
      apply integral_congr_ae
      filter_upwards [edgeX_qmp.ae hK] with p hp
      change K (p.1.2,p.1.1)=K (p.1.1,p.1.2) at hp
      change K p.1*M (p.1.2,p.2)*L (p.1.1,p.2)=
        K (p.1.2,p.1.1)*L (p.1.1,p.2)*M (p.1.2,p.2)
      rw [hp]; ring
    _=_ := hσ.integral_comp σ.measurableEmbedding
      (fun p => K p.1*L (p.1.2,p.2)*M (p.1.1,p.2))

/-- All six permutations have the same mixed triangle integral. -/
theorem mixedTriangle_permutations (K L M : ℝ×ℝ → ℝ)
    (hK : AEKerSymmetric K) (hL : AEKerSymmetric L) (hM : AEKerSymmetric M) :
    mixedTriangle K M L=mixedTriangle K L M ∧
    mixedTriangle M K L=mixedTriangle K L M ∧
    mixedTriangle L M K=mixedTriangle K L M ∧
    mixedTriangle L K M=mixedTriangle K L M ∧
    mixedTriangle M L K=mixedTriangle K L M := by
  have h1 := mixedTriangle_swap_right K L M hK
  have h2 := mixedTriangle_cycle K L M hL hM
  have h3 := (mixedTriangle_cycle M K L hK hL).trans h2
  exact ⟨h1,h2,h3,(mixedTriangle_swap_right L M K hL).trans h3,
    (mixedTriangle_swap_right M K L hM).trans h2⟩

/-- Fubini identifies the mixed term with the actual signed codegree kernel. -/
theorem mixedTriangle_codegree {Y W : ℝ×ℝ → ℝ}
    (hY : BoundedObservable squareMeasure Y) (hW : BoundedObservable squareMeasure W) :
    mixedTriangle Y W W=∫ p, Y p*signedCodegree W p ∂squareMeasure := by
  unfold mixedTriangle
  rw [integral_prod _ (mixedTriangle_integrable hY hW hW)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change (∫ z, Y p*W (p.2,z)*W (p.1,z) ∂unitMeasure)=_
    rw [show (fun z => Y p*W (p.2,z)*W (p.1,z))=(fun z => Y p*(W (p.1,z)*W (p.2,z))) by funext z; ring,
      integral_const_mul]
    rfl

theorem mixedTriangle_add_left {K Y L M : ℝ×ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hY : BoundedObservable squareMeasure Y)
    (hL : BoundedObservable squareMeasure L) (hM : BoundedObservable squareMeasure M) :
    mixedTriangle (fun p => K p+Y p) L M=mixedTriangle K L M+mixedTriangle Y L M := by
  unfold mixedTriangle
  simpa only [add_mul] using integral_add (mixedTriangle_integrable hK hL hM) (mixedTriangle_integrable hY hL hM)

theorem mixedTriangle_add_middle {K L Y M : ℝ×ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hL : BoundedObservable squareMeasure L)
    (hY : BoundedObservable squareMeasure Y) (hM : BoundedObservable squareMeasure M) :
    mixedTriangle K (fun p => L p+Y p) M=mixedTriangle K L M+mixedTriangle K Y M := by
  unfold mixedTriangle
  simpa only [mul_add,add_mul] using integral_add (mixedTriangle_integrable hK hL hM) (mixedTriangle_integrable hK hY hM)

theorem mixedTriangle_add_right {K L M Y : ℝ×ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hL : BoundedObservable squareMeasure L)
    (hM : BoundedObservable squareMeasure M) (hY : BoundedObservable squareMeasure Y) :
    mixedTriangle K L (fun p => M p+Y p)=mixedTriangle K L M+mixedTriangle K L Y := by
  unfold mixedTriangle
  simpa only [mul_add] using integral_add (mixedTriangle_integrable hK hL hM) (mixedTriangle_integrable hK hL hY)

/-- Full perturbation identity `eq:texp`, valid for arbitrary bounded symmetric real kernels. -/
theorem signedTriangle_add_expansion {W Y : ℝ×ℝ → ℝ}
    (hW : BoundedObservable squareMeasure W) (hY : BoundedObservable squareMeasure Y)
    (hWs : AEKerSymmetric W) (hYs : AEKerSymmetric Y) :
    signedTriangle (fun p => W p+Y p)=signedTriangle W+
      3*(∫ p, Y p*signedCodegree W p ∂squareMeasure)+3*mixedTriangle Y Y W+signedTriangle Y := by
  change mixedTriangle (fun p => W p+Y p) (fun p => W p+Y p) (fun p => W p+Y p)=_
  rw [mixedTriangle_add_left hW hY (hW.add hY) (hW.add hY),
    mixedTriangle_add_middle hW hW hY (hW.add hY),
    mixedTriangle_add_middle hY hW hY (hW.add hY),
    mixedTriangle_add_right hW hW hW hY,mixedTriangle_add_right hW hY hW hY,
    mixedTriangle_add_right hY hW hW hY,mixedTriangle_add_right hY hY hW hY]
  have h1 : mixedTriangle W Y W=mixedTriangle Y W W := mixedTriangle_cycle Y W W hWs hWs
  have h2 : mixedTriangle W W Y=mixedTriangle Y W W := (mixedTriangle_cycle W Y W hYs hWs).trans h1
  have h3 : mixedTriangle W Y Y=mixedTriangle Y Y W := mixedTriangle_cycle Y Y W hYs hWs
  have h4 : mixedTriangle Y W Y=mixedTriangle Y Y W := mixedTriangle_swap_right Y Y W hYs
  rw [h1,h2,h3,h4, mixedTriangle_codegree hY hW]
  change signedTriangle W+_+(_+_)+(_+_+(_+signedTriangle Y))=_
  ring

/-- If the other two kernels are bounded by one, the mixed triangle is bounded by the first kernel's L¹ norm. -/
theorem abs_mixedTriangle_le_l1 {K L M : ℝ×ℝ → ℝ}
    (hK : BoundedObservable squareMeasure K) (hL : BoundedObservable squareMeasure L)
    (hM : BoundedObservable squareMeasure M)
    (hLb : ∀ᵐ p ∂squareMeasure, |L p|≤1) (hMb : ∀ᵐ p ∂squareMeasure, |M p|≤1) :
    |mixedTriangle K L M|≤∫ p, |K p| ∂squareMeasure := by
  have hi : Integrable (fun p => |K p|) squareMeasure := by simpa only [Real.norm_eq_abs] using hK.integrable.norm
  calc
    _≤∫ p : (ℝ×ℝ)×ℝ, |K p.1*L (p.1.2,p.2)*M (p.1.1,p.2)| ∂tripleMeasure := by
      simpa only [mixedTriangle,Real.norm_eq_abs] using norm_integral_le_integral_norm
        (f:=fun p : (ℝ×ℝ)×ℝ => K p.1*L (p.1.2,p.2)*M (p.1.1,p.2)) (μ:=tripleMeasure)
    _≤∫ p : (ℝ×ℝ)×ℝ, |K p.1| ∂tripleMeasure := by
      apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using (mixedTriangle_integrable hK hL hM).norm)
        (hi.comp_fst unitMeasure)
      filter_upwards [edgeY_qmp.ae hLb,edgeZ_qmp.ae hMb] with p hp hq
      rw [abs_mul,abs_mul]
      exact (mul_le_mul_of_nonneg_left hq (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using mul_le_mul_of_nonneg_left hp (abs_nonneg (K p.1)))
    _=_ := by rw [integral_prod _ (hi.comp_fst unitMeasure)]; simp

end SparseLowerTail.Section02
