import SparseLowerTail.Section07.RowSeparation

/-! Structural Step 3: large opposite-block row means force small edge values
on both same-block rectangles, through the actual codegree and Euler equation. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section07
open Section04

/-- The elementary product inequality fg≥f+g−1, integrated over a set. -/
theorem codegree_ge_block_means {P : Set ℝ} (hp : 0<unitMeasure.real P)
    {U : Graphon} {x y : ℝ}
    (hx : BoundedObservable unitMeasure (fun z => U (x,z)))
    (hy : BoundedObservable unitMeasure (fun z => U (y,z)))
    (hxb : ∀ᵐ z ∂unitMeasure, U (x,z)∈Icc (0:ℝ) 1)
    (hyb : ∀ᵐ z ∂unitMeasure, U (y,z)∈Icc (0:ℝ) 1) :
    unitMeasure.real P*(setAverage P (fun z => U (x,z))+setAverage P (fun z => U (y,z))-1)
      ≤codegree U x y := by
  have hip := (hx.mul hy).integrable
  have hinonneg : ∀ᵐ z ∂unitMeasure, 0≤U (x,z)*U (y,z) := by
    filter_upwards [hxb,hyb] with z hxz hyz
    exact mul_nonneg hxz.1 hyz.1
  have hrest := setIntegral_le_integral (s := P) hip hinonneg
  have hisum : Integrable (fun z => U (x,z)+U (y,z)) unitMeasure := hx.integrable.add hy.integrable
  have himinus : Integrable (fun z => U (x,z)+U (y,z)-1) unitMeasure := hisum.sub (integrable_const _)
  have hlow : (∫ z in P, (U (x,z)+U (y,z)-1) ∂unitMeasure)≤
      ∫ z in P, U (x,z)*U (y,z) ∂unitMeasure := by
    apply integral_mono_ae himinus.integrableOn hip.integrableOn
    filter_upwards [ae_restrict_of_ae hxb,ae_restrict_of_ae hyb] with z hxz hyz
    nlinarith [mul_nonneg (sub_nonneg.mpr hxz.2) (sub_nonneg.mpr hyz.2)]
  have he : (∫ z in P, (U (x,z)+U (y,z)-1) ∂unitMeasure)=
      unitMeasure.real P*(setAverage P (fun z => U (x,z))+setAverage P (fun z => U (y,z))-1) := by
    rw [integral_sub hisum.integrableOn (integrable_const _),
      integral_add hx.integrable.integrableOn hy.integrable.integrableOn,setIntegral_const]
    dsimp [setAverage]
    field_simp
  rw [he] at hlow
  exact hlow.trans hrest

/-- Actual codegrees are larger than .27 on each same-sign rectangle. -/
theorem smallTarget_sameBlock_codegree (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ p ∂squareMeasure, (p.1∈P ↔ p.2∈P) → (27/100:ℝ)<codegree U p.1 p.2 := by
  dsimp only
  let P := positiveSignBlock (S.eigenfunction 0)
  have hblocks := smallTarget_eigenfunction_blocks external hSampling hr hU S
  have herr := smallTarget_error_bounds external hSampling hr hU S
  have hp : (498/1000:ℝ)<unitMeasure.real P := by linarith [hblocks.2.1,herr.2.2.2.1]
  have hq : (498/1000:ℝ)<unitMeasure.real Pᶜ := by linarith [hblocks.2.2.2.1,herr.2.2.2.1]
  have hrows := boundedObservable_sections (graphon_boundedObservable U)
  have hbounds := Measure.ae_ae_of_ae_prod U.bounded
  have hop := smallTarget_oppositeBlock_means external hSampling hr hU S
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hrows,Measure.quasiMeasurePreserving_snd.ae hrows,
    Measure.quasiMeasurePreserving_fst.ae hbounds,Measure.quasiMeasurePreserving_snd.ae hbounds,
    Measure.quasiMeasurePreserving_fst.ae hop,Measure.quasiMeasurePreserving_snd.ae hop] with p hx hy hxb hyb hxp hyp
  intro hsame
  have hstep {Q : Set ℝ} (hQ : (498/1000:ℝ)<unitMeasure.real Q)
      (hu : (775/1000:ℝ)<setAverage Q (fun z => U (p.1,z)))
      (hv : (775/1000:ℝ)<setAverage Q (fun z => U (p.2,z))) :
      (27/100:ℝ)<codegree U p.1 p.2 := by
    have hh := codegree_ge_block_means (by linarith : 0<unitMeasure.real Q) hx hy hxb hyb
    have hsum : (55/100:ℝ)<setAverage Q (fun z => U (p.1,z))+setAverage Q (fun z => U (p.2,z))-1 := by linarith
    have hprod := mul_lt_mul hQ hsum.le (by norm_num : (0:ℝ)<55/100) (by linarith : 0≤unitMeasure.real Q)
    nlinarith
  by_cases hxin : p.1∈P
  · exact hstep hq (hxp.2.1 hxin) (hyp.2.1 (hsame.mp hxin))
  · exact hstep hp (hxp.2.2 hxin) (hyp.2.2 (fun hyin => hxin (hsame.mpr hyin)))

/-- The actual small same-block cap from the Euler equation. -/
theorem smallTarget_sameBlock_cap (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) {r : ℝ} (hr : r∈Ioc (0:ℝ) smallTarget)
    {U : Graphon} (hU : IsMinimizer r U) (S : KernelSpectralExpansion (centeredKernel U)) :
    let P := positiveSignBlock (S.eigenfunction 0)
    ∀ᵐ p ∂squareMeasure, (p.1∈P ↔ p.2∈P) → U p≤Real.exp (-((27/100)*graphonMultiplier U r)) := by
  dsimp only
  have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr.1,hr.2.trans_lt smallTarget_mem_unit.2⟩
  have hμ := minimizer_multiplier_pos hr01 hU
  filter_upwards [smallTarget_sameBlock_codegree external hSampling hr hU S,
    minimizer_exp_equation hr01 hU] with p hc he
  intro hsame
  rw [he]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (hc hsame).le hμ.le
  nlinarith

end SparseLowerTail.Section07
