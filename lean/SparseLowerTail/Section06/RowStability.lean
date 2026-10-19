import SparseLowerTail.Section06.TwoWellRows
import SparseLowerTail.Section02.WeightedCut

/-! Quantitative Steps 1--2 of local rigidity: cut closeness controls the
entire row functional, hence forces every minimizing row near one of two wells. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04

theorem rowQuadratic_integrable (U : Graphon) {v : ℝ → ℝ}
    (hv : AEMeasurable v unitMeasure) (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    Integrable (fun p : ℝ × ℝ => v p.1*U p*v p.2) squareMeasure := by
  have h := profile_boundedObservable hv hb
  exact (((h.comp Measure.quasiMeasurePreserving_fst).mul (graphon_boundedObservable U)).mul
    (h.comp Measure.quasiMeasurePreserving_snd)).integrable

theorem rowQuadratic_mem (U : Graphon) {v : ℝ → ℝ}
    (hv : AEMeasurable v unitMeasure) (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    rowQuadratic U v∈Icc (0:ℝ) 1 := by
  have hbd : ∀ᵐ p : ℝ × ℝ ∂squareMeasure,v p.1*U p*v p.2∈Icc (0:ℝ) 1 := by
    filter_upwards [U.bounded,Measure.quasiMeasurePreserving_fst.ae hb,
      Measure.quasiMeasurePreserving_snd.ae hb] with p hp hx hy
    have hh := mul_le_mul hx.2 hp.2 hp.1 (by norm_num : (0:ℝ)≤1)
    simp only [one_mul] at hh
    exact ⟨mul_nonneg (mul_nonneg hx.1 hp.1) hy.1,
      by simpa using mul_le_mul hh hy.2 hy.1 (by norm_num : (0:ℝ)≤1)⟩
  refine ⟨integral_nonneg_of_ae (hbd.mono fun _ h => h.1),?_⟩
  have h := integral_mono_ae (rowQuadratic_integrable U hv hb)
    (integrable_const (μ:=squareMeasure) (1:ℝ)) (hbd.mono fun _ h => h.2)
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h

theorem rowQuadratic_cut_bound (U W : Graphon) {v : ℝ → ℝ}
    (hv : AEMeasurable v unitMeasure) (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    |rowQuadratic U v-rowQuadratic W v|≤cutNorm (fun p => U p-W p) := by
  have he : rowQuadratic U v-rowQuadratic W v=
      ∫ p,v p.1*v p.2*(U p-W p) ∂squareMeasure := by
    rw [rowQuadratic,rowQuadratic,← integral_sub (rowQuadratic_integrable U hv hb)
      (rowQuadratic_integrable W hv hb)]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by ring
  rw [he]
  exact abs_weighted_integral_le_cutNorm ((graphon_integrable U).sub (graphon_integrable W)) hv hv hb hb

/-- The uniform bound in `s6:beta`, for arbitrary graphons and admissible profiles. -/
theorem rowFunctional_cut_bound (U W : Graphon) {ν μ : ℝ} (hν : 0≤ν)
    {v : ℝ → ℝ} (hv : AEMeasurable v unitMeasure)
    (hb : ∀ᵐ x ∂unitMeasure,v x∈Icc (0:ℝ) 1) :
    |rowFunctional U ν v-rowFunctional W μ v|≤ν*cutNorm (fun p => U p-W p)+|ν-μ| := by
  have hq := rowQuadratic_cut_bound U W hv hb
  have hw := rowQuadratic_mem W hv hb
  have he : rowFunctional U ν v-rowFunctional W μ v=
      ν*(rowQuadratic U v-rowQuadratic W v)+(ν-μ)*rowQuadratic W v := by
    unfold rowFunctional
    ring
  rw [he]
  calc
    _ ≤ |ν*(rowQuadratic U v-rowQuadratic W v)|+|(ν-μ)*rowQuadratic W v| := abs_add_le _ _
    _ = ν*|rowQuadratic U v-rowQuadratic W v|+|ν-μ| *rowQuadratic W v := by
      rw [abs_mul,abs_mul,abs_of_nonneg hν,abs_of_nonneg hw.1]
    _ ≤ ν*cutNorm (fun p => U p-W p)+|ν-μ| := by
      have h1 := mul_le_mul_of_nonneg_left hq hν
      have h2 := mul_le_mul_of_nonneg_left hw.2 (abs_nonneg (ν-μ))
      nlinarith

/-- Every minimizing row has uniformly small squared distance to one of the two
balanced profiles. This is the actual graphon assertion in Step 2 of `thm:rigidity`. -/
theorem minimizer_rows_near_balanced (hSampling : UniformSampling)
    {P : Set ℝ} (hP : MeasurableSet P) (hm : unitMeasure P=(1/2:ENNReal))
    {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1) (hμ : 0<μ)
    (hEL : BalancedEL a b μ) :
    ∃ c : ℝ,0<c ∧ ∀ (r : ℝ) (U : Graphon),r∈Ioo (0:ℝ) 1 → IsMinimizer r U →
      let B := twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩
      ∀ᵐ x ∂unitMeasure,
        c*min (profileL2Sq (fun y => U (x,y)) (blockProfile P a b))
          (profileL2Sq (fun y => U (x,y)) (blockProfile P b a))≤
          2*(graphonMultiplier U r*cutNorm (fun p => U p-B p)+|graphonMultiplier U r-μ|) := by
  obtain ⟨c,hc,hgrowth⟩ := rowFunctional_two_well_growth hP hm ha hab hb hμ hEL
  refine ⟨c,hc,?_⟩
  intro r U hr hU
  dsimp only
  let B := twoBlock P hP a b ⟨ha.le,(hab.trans hb).le⟩ ⟨(ha.trans hab).le,hb.le⟩
  have hν := (minimizer_multiplier_pos hr hU).le
  have hf := blockProfile_boundedObservable hP a b
  have hfb : ∀ᵐ y ∂unitMeasure,blockProfile P a b y∈Icc (0:ℝ) 1 := by
    apply Eventually.of_forall
    intro y
    simp only [blockProfile]
    split_ifs
    · exact ⟨ha.le,(hab.trans hb).le⟩
    · exact ⟨(ha.trans hab).le,hb.le⟩
  have hfixed := rowFunctional_cut_bound U B (μ:=μ) hν hf.measurable hfb
  filter_upwards [minimizer_row_functional hSampling hr hU,
    minimizer_rows_minimize hSampling hr hU] with x hx hxmin
  have hrow := rowFunctional_cut_bound U B (μ:=μ) hν hx.1 hx.2.1
  have hmin := hxmin _ hf.measurable hfb
  have hg := hgrowth _ hx.1 hx.2.1
  have h1 := (abs_le.mp hrow).1
  have h2 := (abs_le.mp hfixed).2
  change c*min (profileL2Sq (fun y => U (x,y)) (blockProfile P a b))
    (profileL2Sq (fun y => U (x,y)) (blockProfile P b a))≤
    2*(graphonMultiplier U r*cutNorm (fun p => U p-B p)+|graphonMultiplier U r-μ|)
  change c*min (profileL2Sq (fun y => U (x,y)) (blockProfile P a b))
    (profileL2Sq (fun y => U (x,y)) (blockProfile P b a))≤
    rowFunctional B μ (fun y => U (x,y))-rowFunctional B μ (blockProfile P a b) at hg
  linarith

end SparseLowerTail.Section06
