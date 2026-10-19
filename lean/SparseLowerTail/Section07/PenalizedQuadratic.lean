import SparseLowerTail.Section07.PenalizedSecondVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Extension of the penalized second variation from normalized bounded tests
to every integrable mean-zero test, and therefore to every L² test. Since the
graphon is bounded, L¹ dominated convergence suffices for this extension. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section07
open Section04

/-- Removing the normalization of the bounded vertex test. -/
theorem penalized_quadratic_nonpos_bounded (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {f : ℝ → ℝ} (hf : BoundedObservable unitMeasure f)
    (hm : ∫ x, f x ∂unitMeasure=0) :
    (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)≤0 := by
  obtain ⟨K,hK,hfK⟩ := hf.bound
  let c := K+1
  have hc : 0<c := by dsimp [c]; linarith
  let ψ := fun x => f x/c
  have hψ : AEMeasurable ψ unitMeasure := hf.measurable.div_const c
  have hb : ∀ᵐ x ∂unitMeasure, |ψ x|≤1 := by
    filter_upwards [hfK] with x hx
    dsimp [ψ]
    rw [abs_div,abs_of_pos hc]
    apply (div_le_one hc).mpr
    have hx' : |f x|≤K := hx
    dsimp [c]
    linarith
  have hmean : ∫ x, ψ x ∂unitMeasure=0 := by simp [ψ,integral_div,hm]
  have hh := penalized_quadratic_nonpos_unit hSampling hr hγ hU hpen hψ hb hmean
  have he : (∫ p, U p*(ψ p.1*ψ p.2) ∂squareMeasure)=
      (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)/c^2 := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp [ψ]; field_simp
  rw [he] at hh
  simpa only [zero_mul] using (div_le_iff₀ (sq_pos_of_pos hc)).mp hh

/-- Symmetric clipping, used only to approximate an integrable vertex test. -/
def quadraticClip (n : ℕ) (x : ℝ) : ℝ := max (-(n:ℝ)) (min (n:ℝ) x)

theorem quadraticClip_continuous (n : ℕ) : Continuous (quadraticClip n) := by
  unfold quadraticClip
  fun_prop

theorem quadraticClip_abs_le (n : ℕ) (x : ℝ) : |quadraticClip n x|≤|x| := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  unfold quadraticClip
  by_cases hx : x≤n
  · rw [min_eq_right hx]
    by_cases hl : -(n:ℝ)≤x
    · rw [max_eq_right hl]
    · rw [max_eq_left (le_of_not_ge hl),abs_neg,abs_of_nonneg hn]
      have hx0 : x≤0 := by linarith
      rw [abs_of_nonpos hx0]
      linarith
  · rw [min_eq_left (le_of_not_ge hx),max_eq_right (by linarith : -(n:ℝ)≤n),abs_of_nonneg hn]
    have hx0 : 0≤x := by linarith
    rw [abs_of_nonneg hx0]
    linarith

theorem quadraticClip_bound (n : ℕ) (x : ℝ) : |quadraticClip n x|≤n := by
  rw [abs_le]
  unfold quadraticClip
  exact ⟨le_max_left _ _,max_le (by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith) (min_le_left _ _)⟩

theorem quadraticClip_tendsto (x : ℝ) : Tendsto (fun n => quadraticClip n x) atTop (𝓝 x) := by
  obtain ⟨N,hN⟩ := exists_nat_gt |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnx : |x|≤(n:ℝ) := hN.le.trans (Nat.cast_le.mpr hn)
  have hh := abs_le.mp hnx
  simp only [quadraticClip,min_eq_right hh.2,max_eq_right hh.1]

/-- The full quadratic-form conclusion of `lem:penalized`, in the stronger
L¹ formulation. No graphon spectral representation is needed for this step. -/
theorem penalized_quadratic_nonpos_integrable (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {f : ℝ → ℝ} (hf : Integrable f unitMeasure)
    (hm : ∫ x, f x ∂unitMeasure=0) :
    (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)≤0 := by
  let g := fun n x => quadraticClip n (f x)
  have hg (n : ℕ) : BoundedObservable unitMeasure (g n) := by
    refine ⟨(quadraticClip_continuous n).measurable.comp_aemeasurable hf.aemeasurable,
      n,Nat.cast_nonneg n,?_⟩
    exact Eventually.of_forall fun x => quadraticClip_bound n (f x)
  have hglim (x : ℝ) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := quadraticClip_tendsto (f x)
  have hgabs (n : ℕ) (x : ℝ) : |g n x|≤|f x| := quadraticClip_abs_le n (f x)
  have hmeanlim : Tendsto (fun n => ∫ x, g n x ∂unitMeasure) atTop (𝓝 0) := by
    rw [← hm]
    exact tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hg n).measurable.aestronglyMeasurable) hf.norm
      (fun n => Eventually.of_forall (hgabs n)) (Eventually.of_forall hglim)
  let M := ∫ x, |f x| ∂unitMeasure
  have hM : 0≤M := integral_nonneg fun x => abs_nonneg _
  have hmeanbound (n : ℕ) : |∫ x, g n x ∂unitMeasure|≤M := by
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono (hg n).integrable.norm hf.norm (hgabs n))
  let fn := fun n x => g n x-(∫ y, g n y ∂unitMeasure)
  have hfn (n : ℕ) : BoundedObservable unitMeasure (fn n) := by
    convert (hg n).add ((BoundedObservable.const (∫ y, g n y ∂unitMeasure)).const_mul (-1)) using 1
    funext x
    dsimp [fn]
    ring
  have hfnmean (n : ℕ) : ∫ x, fn n x ∂unitMeasure=0 := by
    simp [fn,integral_sub (hg n).integrable (integrable_const _)]
  have hfnlim (x : ℝ) : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    simpa only [sub_zero] using (hglim x).sub hmeanlim
  have hfnbound (n : ℕ) (x : ℝ) : |fn n x|≤|f x|+M := by
    exact (abs_sub _ _).trans (add_le_add (hgabs n x) (hmeanbound n))
  have hq (n : ℕ) : (∫ p, U p*(fn n p.1*fn n p.2) ∂squareMeasure)≤0 :=
    penalized_quadratic_nonpos_bounded hSampling hr hγ hU hpen (hfn n) (hfnmean n)
  have hd : Integrable (fun p : ℝ × ℝ => (|f p.1|+M)*(|f p.2|+M)) squareMeasure :=
    (hf.norm.add (integrable_const M)).mul_prod (hf.norm.add (integrable_const M))
  have hlim : Tendsto (fun n => ∫ p, U p*(fn n p.1*fn n p.2) ∂squareMeasure) atTop
      (𝓝 (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun p => (|f p.1|+M)*(|f p.2|+M))
    · intro n
      exact ((graphon_boundedObservable U).mul (((hfn n).comp Measure.quasiMeasurePreserving_fst).mul
        ((hfn n).comp Measure.quasiMeasurePreserving_snd))).measurable.aestronglyMeasurable
    · exact hd
    · intro n
      filter_upwards [U.bounded] with p hp
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hp.1]
      calc
        U p*(|fn n p.1| *|fn n p.2|)≤1*(|fn n p.1| *|fn n p.2|) := by
          gcongr
          exact hp.2
        _ ≤ (|f p.1|+M)*(|f p.2|+M) := by
          rw [one_mul]
          exact mul_le_mul (hfnbound n p.1) (hfnbound n p.2) (abs_nonneg _) (by positivity)
    · exact Eventually.of_forall fun p => tendsto_const_nhds.mul ((hfnlim p.1).mul (hfnlim p.2))
  exact le_of_tendsto hlim (Eventually.of_forall hq)

/-- Absolute integrability of the graphon quadratic integrand. -/
theorem graphon_quadratic_integrable (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    Integrable (fun p => U p*(f p.1*f p.2)) squareMeasure := by
  apply (hf.mul_prod hf).bdd_mul' U.measurable.aestronglyMeasurable
  filter_upwards [U.bounded] with p hp
  simpa only [Real.norm_eq_abs,abs_of_nonneg hp.1] using hp.2

/-- Product-integral and iterated operator forms of the quadratic form agree. -/
theorem graphon_quadratic_eq_iterated (U : Graphon) {f : ℝ → ℝ}
    (hf : Integrable f unitMeasure) :
    (∫ p, U p*(f p.1*f p.2) ∂squareMeasure)=
      ∫ x, f x*(∫ y, U (x,y)*f y ∂unitMeasure) ∂unitMeasure := by
  rw [integral_prod _ (graphon_quadratic_integrable U hf)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring

/-- The exact L²-test conclusion of `lem:penalized`, written as ⟨f,T_U f⟩. -/
theorem penalized_quadratic_nonpos_L2 (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W)
    {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure)
    (hm : ∫ x, f x ∂unitMeasure=0) :
    (∫ x, f x*(∫ y, U (x,y)*f y ∂unitMeasure) ∂unitMeasure)≤0 := by
  have hi := MemLp.integrable (by norm_num : (1:ENNReal)≤2) hf
  rw [← graphon_quadratic_eq_iterated U hi]
  exact penalized_quadratic_nonpos_integrable hSampling hr hγ hU hpen hi hm

/-- Both conclusions of `lem:penalized`, with the sampling realization explicit. -/
theorem penalized_minimizer_data (hSampling : UniformSampling)
    {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ) {U : Graphon}
    (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W) :
    graphonMultiplier U r=3*γ ∧
    ∀ f : ℝ → ℝ, MemLp f 2 unitMeasure → (∫ x, f x ∂unitMeasure)=0 →
      (∫ x, f x*(∫ y, U (x,y)*f y ∂unitMeasure) ∂unitMeasure)≤0 :=
  ⟨minimizer_multiplier_eq_three_penalty hr hγ hU hpen,
    fun _ hf hm => penalized_quadratic_nonpos_L2 hSampling hr hγ hU hpen hf hm⟩

end SparseLowerTail.Section07
