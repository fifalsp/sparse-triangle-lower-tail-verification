import SparseLowerTail.Section04.Branch
import SparseLowerTail.Section04.EntropyGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Scalar two-well analysis underlying manuscript `thm:twowell`. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section04

/-- The exact two-variable reduction of the insertion functional at a balanced graphon. -/
def scalarWell (a b μ u w : ℝ) : ℝ :=
  entropy u+entropy w+μ/4*(a*(u^2+w^2)+2*b*u*w)

@[simp] theorem scalarWell_swap (a b μ u w : ℝ) :
    scalarWell a b μ u w=scalarWell a b μ w u := by unfold scalarWell; ring

/-- The strictly increasing scalar function used to classify off-diagonal critical points. -/
def wellShape (α c y : ℝ) : ℝ :=
  Real.log (y/Real.sinh y)-Real.log c+(1+2*α/c)*(y*Real.cosh y/Real.sinh y)

theorem sinh_sq_gt_sq {y : ℝ} (hy : 0<y) : y^2<(Real.sinh y)^2 := by
  have h := Real.self_lt_sinh_iff.mpr hy
  nlinarith

/-- A logarithmic-mean inequality giving strict Hessian nondegeneracy. -/
theorem log_difference_sq_mul_lt {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (Real.log b-Real.log a)^2*(a*b)<(b-a)^2 := by
  have hb : 0<b := ha.trans hab
  let y := (Real.log b-Real.log a)/2
  let t := Real.exp ((Real.log a+Real.log b)/2)
  have hy : 0<y := by dsimp [y]; linarith [Real.strictMonoOn_log ha hb hab]
  have ht : 0<t := Real.exp_pos _
  have heplus : t*Real.exp y=b := by
    rw [← Real.exp_add]
    convert Real.exp_log hb using 1
    dsimp [y]
    congr 1
    ring
  have heminus : t*Real.exp (-y)=a := by
    rw [← Real.exp_add]
    convert Real.exp_log ha using 1
    dsimp [y]
    congr 1
    ring
  have hd : b-a=2*t*Real.sinh y := by
    rw [Real.sinh_eq]
    nlinarith [heplus,heminus]
  have habt : a*b=t^2 := by
    have he : Real.exp y*Real.exp (-y)=1 := by rw [← Real.exp_add]; simp
    nlinarith [heplus,heminus,mul_pos ht ht,
      show (t*Real.exp y)*(t*Real.exp (-y))=t^2 by nlinarith [he]]
  have hs := sinh_sq_gt_sq hy
  have hp := mul_lt_mul_of_pos_left hs (sq_pos_of_pos ht)
  have hlog : Real.log b-Real.log a=2*y := by dsimp [y]; ring
  rw [hlog,habt,hd]
  nlinarith

/-- The determinant of the Hessian at either ordered off-diagonal EL well is positive. -/
theorem wellHessian_det_pos {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    0<(1/a+μ*a/2)*(1/b+μ*a/2)-(μ*b/2)^2 := by
  have hb : 0<b := ha.trans hab
  let α := μ*a/2
  let β := μ*b/2
  let c := β-α
  have hα : 0<α := by dsimp [α]; positivity
  have hc : 0<c := by dsimp [c,β,α]; nlinarith
  have hd : 0<b-a := sub_pos.mpr hab
  have hp : 0<a*b := mul_pos ha hb
  have hlog : Real.log b-Real.log a=c*(b-a) := by
    rcases hEL with ⟨h1,h2⟩
    dsimp [c,α,β]
    rw [h1,h2]
    ring
  have hs : c^2*(a*b)<1 := by
    have ht := log_difference_sq_mul_lt ha hab
    rw [hlog] at ht
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hd)).mp
    nlinarith only [ht]
  have hlin : 2*c*a*b<a+b := by
    by_contra hn
    have hn' : a+b≤2*c*a*b := le_of_not_gt hn
    have hx := mul_lt_mul_of_pos_right hs (show 0<4*a*b by positivity)
    have hsum : 0<a+b := by positivity
    nlinarith [sq_nonneg (a-b)]
  have he : a*b*((1/a+α)*(1/b+α)-β^2)=
      1-c^2*(a*b)+α*(a+b-2*c*a*b) := by
    dsimp [c]
    field_simp
    ring
  have hpos : 0<a*b*((1/a+α)*(1/b+α)-β^2) := by
    rw [he]
    have := mul_pos hα (sub_pos.mpr hlin)
    linarith
  exact (mul_pos_iff_of_pos_left hp).mp hpos

/-- `thm:twowell` (a), stated directly as strict positivity of the Hessian quadratic form. -/
theorem wellHessian_posDef {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) {x y : ℝ} (hxy : x≠0 ∨ y≠0) :
    0<(1/a+μ*a/2)*x^2+2*(μ*b/2)*x*y+(1/b+μ*a/2)*y^2 := by
  have hb : 0<b := ha.trans hab
  have hA : 0<1/a+μ*a/2 := by positivity
  have hdet := wellHessian_det_pos ha hab hμ hEL
  have he : (1/a+μ*a/2)*
      ((1/a+μ*a/2)*x^2+2*(μ*b/2)*x*y+(1/b+μ*a/2)*y^2) =
      ((1/a+μ*a/2)*x+(μ*b/2)*y)^2+
        ((1/a+μ*a/2)*(1/b+μ*a/2)-(μ*b/2)^2)*y^2 := by ring
  have hp : 0<(1/a+μ*a/2)*
      ((1/a+μ*a/2)*x^2+2*(μ*b/2)*x*y+(1/b+μ*a/2)*y^2) := by
    rw [he]
    by_cases hy : y=0
    · have hx : x≠0 := hxy.resolve_right (by simp only [hy,ne_eq,not_true_eq_false,not_false_eq_true])
      simp only [hy,mul_zero,add_zero,zero_pow (by omega : 2≠0)]
      exact sq_pos_of_ne_zero (mul_ne_zero hA.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hy))
  exact (mul_pos_iff_of_pos_left hA).mp hp

theorem sinh_mul_cosh_gt {y : ℝ} (hy : 0<y) : y<Real.sinh y*Real.cosh y := by
  have h := Real.self_lt_sinh_iff.mpr (show 0<2*y by linarith)
  rw [Real.sinh_two_mul] at h
  linarith

theorem hasDerivAt_wellShape {α c y : ℝ} (hc : 0<c) (hy : 0<y) :
    HasDerivAt (wellShape α c)
      ((1/y-y/(Real.sinh y)^2)+(2*α/c)*(Real.cosh y/Real.sinh y-y/(Real.sinh y)^2)) y := by
  have hs : 0<Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hi := hasDerivAt_id y
  have hrat := hi.div (Real.hasDerivAt_sinh y) hs.ne'
  have hlog := (Real.hasDerivAt_log (div_ne_zero hy.ne' hs.ne')).comp y hrat
  have hprod := (hi.mul (Real.hasDerivAt_cosh y)).div (Real.hasDerivAt_sinh y) hs.ne'
  convert (hlog.sub_const (Real.log c)).add (hprod.const_mul (1+2*α/c)) using 1
  simp only [id_eq,Pi.mul_apply]
  field_simp
  rw [Real.cosh_sq]
  ring

theorem wellShape_deriv_pos {α c y : ℝ} (hα : 0≤α) (hc : 0<c) (hy : 0<y) :
    0<deriv (wellShape α c) y := by
  rw [(hasDerivAt_wellShape hc hy).deriv]
  have hs : 0<Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hsq := sinh_sq_gt_sq hy
  have hsc := sinh_mul_cosh_gt hy
  have hfirst : 0<1/y-y/(Real.sinh y)^2 := by
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (sq_pos_of_pos hs) hy).mpr
    simpa only [pow_two,one_mul] using hsq
  have hsecond : 0<Real.cosh y/Real.sinh y-y/(Real.sinh y)^2 := by
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (sq_pos_of_pos hs) hs).mpr
    nlinarith [mul_pos hs (sub_pos.mpr hsc)]
  exact add_pos_of_pos_of_nonneg hfirst (mul_nonneg (by positivity) hsecond.le)

theorem strictMonoOn_wellShape {α c : ℝ} (hα : 0≤α) (hc : 0<c) :
    StrictMonoOn (wellShape α c) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro y hy
    exact (hasDerivAt_wellShape hc hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    exact wellShape_deriv_pos hα hc hy

/-- The two stationary equations for the reduced insertion functional. -/
def WellCritical (α β u w : ℝ) : Prop :=
  Real.log u+α*u+β*w=0 ∧ Real.log w+β*u+α*w=0

/-- Hyperbolic coordinates turn every ordered positive critical point into a root
of the strictly monotone scalar shape function, and recover its coordinates. -/
theorem wellCritical_coordinates {α β u w : ℝ} (hc : 0<β-α)
    (hu : 0<u) (huw : u<w) (hcrit : WellCritical α β u w) :
    ∃ y t : ℝ, 0<y ∧ 0<t ∧ wellShape α (β-α) y=0 ∧
      (β-α)*t*Real.sinh y=y ∧ u=t*Real.exp (-y) ∧ w=t*Real.exp y := by
  have hw : 0<w := hu.trans huw
  let y := (Real.log w-Real.log u)/2
  let t := Real.exp ((Real.log u+Real.log w)/2)
  have hy : 0<y := by dsimp [y]; linarith [Real.strictMonoOn_log hu hw huw]
  have ht : 0<t := Real.exp_pos _
  have hep : t*Real.exp y=w := by
    rw [← Real.exp_add]
    convert Real.exp_log hw using 1
    dsimp [y]
    congr 1
    ring
  have hem : t*Real.exp (-y)=u := by
    rw [← Real.exp_add]
    convert Real.exp_log hu using 1
    dsimp [y]
    congr 1
    ring
  have hd : w-u=2*t*Real.sinh y := by rw [Real.sinh_eq]; nlinarith
  have hadd : w+u=2*t*Real.cosh y := by rw [Real.cosh_eq]; nlinarith
  have hlt : Real.log t=(Real.log u+Real.log w)/2 := Real.log_exp _
  rcases hcrit with ⟨h1,h2⟩
  have hcy : (β-α)*t*Real.sinh y=y := by dsimp [y]; nlinarith [hd]
  have hlog : Real.log t=-(α+β)*t*Real.cosh y := by
    linear_combination hlt + (h1+h2)/2 - (α+β)/2*hadd
  have hs : 0<Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hrat : y/Real.sinh y=(β-α)*t := (div_eq_iff hs.ne').mpr hcy.symm
  have hroot : wellShape α (β-α) y=0 := by
    unfold wellShape
    rw [hrat,Real.log_mul hc.ne' ht.ne',hlog]
    field_simp
    linear_combination -(α+β)*Real.cosh y*hcy
  exact ⟨y,t,hy,ht,hroot,hcy,hem.symm,hep.symm⟩

/-- There is at most one strictly ordered positive critical point. -/
theorem wellCritical_ordered_unique {α β u w u' w' : ℝ} (hα : 0≤α) (hc : 0<β-α)
    (hu : 0<u) (huw : u<w) (hu' : 0<u') (huw' : u'<w')
    (hcrit : WellCritical α β u w) (hcrit' : WellCritical α β u' w') :
    u=u' ∧ w=w' := by
  obtain ⟨y,t,hy,ht,hr,he,huv,hwv⟩ := wellCritical_coordinates hc hu huw hcrit
  obtain ⟨y',t',hy',ht',hr',he',huv',hwv'⟩ := wellCritical_coordinates hc hu' huw' hcrit'
  have hyy : y=y' := (strictMonoOn_wellShape hα hc).injOn hy hy' (hr.trans hr'.symm)
  subst y'
  have hs : 0<Real.sinh y := Real.sinh_pos_iff.mpr hy
  have htt : t=t' := by nlinarith [mul_pos hc hs]
  subst t'
  exact ⟨huv.trans huv'.symm,hwv.trans hwv'.symm⟩

theorem balancedEL_wellCritical {a b μ : ℝ} (hEL : BalancedEL a b μ) :
    WellCritical (μ*a/2) (μ*b/2) a b := by
  rcases hEL with ⟨ha,hb⟩
  constructor <;> nlinarith

/-- Every positive critical point is diagonal or one of the two EL wells. -/
theorem wellCritical_classification {a b μ u w : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) (hu : 0<u) (hw : 0<w)
    (hcrit : WellCritical (μ*a/2) (μ*b/2) u w) :
    u=w ∨ (u=a ∧ w=b) ∨ (u=b ∧ w=a) := by
  have hα : 0≤μ*a/2 := by positivity
  have hc : 0<μ*b/2-μ*a/2 := by nlinarith
  rcases lt_trichotomy u w with huw | he | hwu
  · exact Or.inr (Or.inl (wellCritical_ordered_unique hα hc hu huw ha hab hcrit
      (balancedEL_wellCritical hEL)))
  · exact Or.inl he
  · have hswap : WellCritical (μ*a/2) (μ*b/2) w u := by
      rcases hcrit with ⟨h1,h2⟩
      constructor <;> linarith
    obtain ⟨he1,he2⟩ := wellCritical_ordered_unique hα hc hw hwu ha hab hswap
      (balancedEL_wellCritical hEL)
    exact Or.inr (Or.inr ⟨he2,he1⟩)

theorem tendsto_wellShape_zero (α c : ℝ) :
    Tendsto (wellShape α c) (𝓝[>] 0) (𝓝 (1+2*α/c-Real.log c)) := by
  have hs : Tendsto (fun y : ℝ => Real.sinh y/y) (𝓝[>] 0) (𝓝 1) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hi : Tendsto (fun y : ℝ => y/Real.sinh y) (𝓝[>] 0) (𝓝 1) := by
    simpa only [inv_div,inv_one] using hs.inv₀ (by norm_num : (1:ℝ)≠0)
  have hl := (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hi
  have hc : Tendsto (fun y : ℝ => Real.cosh y) (𝓝[>] 0) (𝓝 1) := by
    simpa using (Real.continuous_cosh.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have h := (hl.sub_const (Real.log c)).add ((hi.mul hc).const_mul (1+2*α/c))
  convert h using 1
  · funext y
    unfold wellShape
    simp only [Function.comp_apply]
    ring
  · simp
    ring

theorem wellShape_endpoint_lt {α c y : ℝ} (hα : 0≤α) (hc : 0<c) (hy : 0<y) :
    1+2*α/c-Real.log c<wellShape α c y := by
  have hmono := strictMonoOn_wellShape hα hc
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0,wellShape α c x≤wellShape α c (y/2) := by
    have hx : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x := self_mem_nhdsWithin
    have hx' : ∀ᶠ x : ℝ in 𝓝[>] 0,x<y/2 :=
      (eventually_lt_nhds (half_pos hy)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hx,hx'] with x hx hx'
    exact (hmono hx (half_pos hy) hx').le
  have hle := le_of_tendsto (tendsto_wellShape_zero α c) he
  exact hle.trans_lt (hmono (half_pos hy) hy (by linarith))

/-- The unique diagonal stationary point has a strictly negative transverse curvature. -/
theorem diagonal_critical_curvature_neg {a b μ s : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) (hs : 0<s)
    (hcrit : WellCritical (μ*a/2) (μ*b/2) s s) :
    1/s-(μ*b/2-μ*a/2)<0 := by
  let α := μ*a/2
  let β := μ*b/2
  let c := β-α
  have hα : 0≤α := by dsimp [α]; positivity
  have hc : 0<c := by dsimp [c,α,β]; nlinarith
  obtain ⟨y,t,hy,_,hr,_,_,_⟩ := wellCritical_coordinates hc ha hab (balancedEL_wellCritical hEL)
  have hend : 1+2*α/c-Real.log c<0 := by
    have h := wellShape_endpoint_lt hα hc hy
    change wellShape α c y=0 at hr
    rwa [hr] at h
  have hlogs : Real.log s+(α+β)*s=0 := by
    rcases hcrit with ⟨h1,_⟩
    dsimp [α,β]
    linarith
  have hsc : 1/c<s := by
    by_contra hn
    have hle : s≤1/c := le_of_not_gt hn
    have hlogle := Real.strictMonoOn_log.monotoneOn hs (one_div_pos.mpr hc) hle
    have hb : 0<b := ha.trans hab
    have habpos : 0≤α+β := by dsimp [α,β]; positivity
    have hm := mul_le_mul_of_nonneg_left hle habpos
    have hf : Real.log (1/c)+(α+β)*(1/c)=1+2*α/c-Real.log c := by
      rw [Real.log_div one_ne_zero hc.ne',Real.log_one]
      have hn : β-α≠0 := hc.ne'
      dsimp [c]
      field_simp
      ring
    nlinarith [hf]
  have := (div_lt_iff₀ hs).mpr (show 1<c*s by
    have := (div_lt_iff₀ hc).mp hsc
    nlinarith)
  exact sub_neg.mpr this

end SparseLowerTail.Section06
