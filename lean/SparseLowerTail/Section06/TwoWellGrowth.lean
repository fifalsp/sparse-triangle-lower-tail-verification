import SparseLowerTail.Section06.TwoWellMinima
import SparseLowerTail.Section02.Bregman

/-! Quantitative quadratic growth of the scalar insertion functional. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace SparseLowerTail.Section06
open Section04 Section02

/-- A local entropy remainder bound with the sharp limiting coefficient 1/(2s). -/
theorem entropy_remainder_lower {s u R : ℝ} (hs : 0<s) (hu : 0<u)
    (hsR : s≤R) (huR : u≤R) :
    (u-s)^2/(2*R)≤entropy u-entropy s-(u-s)*Real.log s := by
  have hR : 0<R := hs.trans_le hsR
  have hden : ∀ θ∈Icc (0:ℝ) 1,0<s+θ*(u-s) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.2 with h | h
    · rw [h]; simpa using hu
    · nlinarith [mul_pos (sub_pos.mpr h) hs,mul_nonneg hθ.1 hu.le]
  have hdenR : ∀ θ∈Icc (0:ℝ) 1,s+θ*(u-s)≤R := by
    intro θ hθ
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hsR),
      mul_nonneg hθ.1 (sub_nonneg.mpr huR)]
  have hc : ContinuousOn (fun θ : ℝ => (1-θ)/(s+θ*(u-s))) (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun θ hθ => (hden θ hθ).ne'
  have hi : IntervalIntegrable (fun θ : ℝ => (1-θ)/(s+θ*(u-s))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hlo : IntervalIntegrable (fun θ : ℝ => (1-θ)/R) volume 0 1 := by
    exact ((continuous_const.sub continuous_id).div_const R).intervalIntegrable _ _
  have hib := intervalIntegral.integral_mono_on (a:=0) (b:=1) (by norm_num) hlo hi
    (fun θ hθ => div_le_div_of_nonneg_left (sub_nonneg.mpr hθ.2) (hden θ hθ) (hdenR θ hθ))
  have he : (∫ θ in (0:ℝ)..1,(1-θ)/R)=1/(2*R) := by
    rw [intervalIntegral.integral_div,intervalIntegral.integral_sub
      (show IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 from intervalIntegrable_const)
      (show IntervalIntegrable (fun θ : ℝ => θ) volume 0 1 from continuous_id.intervalIntegrable _ _)]
    norm_num
    ring
  rw [he] at hib
  rw [bregman_remainder hs hu]
  have h := mul_le_mul_of_nonneg_left hib (sq_nonneg (u-s))
  simpa only [bregmanRatio,div_eq_mul_inv,one_mul] using h

private theorem quadratic_nonneg {A B C x y : ℝ} (hA : 0<A) (hd : 0≤A*C-B^2) :
    0≤A*x^2+2*B*x*y+C*y^2 := by
  have he : A*(A*x^2+2*B*x*y+C*y^2)=(A*x+B*y)^2+(A*C-B^2)*y^2 := by ring
  have hp : 0≤A*(A*x^2+2*B*x*y+C*y^2) := by
    rw [he]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hd (sq_nonneg _))
  exact (mul_nonneg_iff_of_pos_left hA).mp hp

/-- The positive Hessian remains uniformly positive after small denominator and diagonal changes. -/
theorem exists_wellHessian_margin {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ δ : ℝ,0<δ ∧ ∀ x y : ℝ,
      δ*(x^2+y^2)≤(1/(a+δ)+μ*a/2)*x^2+2*(μ*b/2)*x*y+(1/(b+δ)+μ*a/2)*y^2 := by
  have hb : 0<b := ha.trans hab
  let A := fun t : ℝ => 1/(a+t)+μ*a/2-t
  let C := fun t : ℝ => 1/(b+t)+μ*a/2-t
  have hAc : ContinuousAt A 0 := by dsimp [A]; fun_prop (disch := simpa using ha.ne')
  have hCc : ContinuousAt C 0 := by dsimp [C]; fun_prop (disch := simpa using hb.ne')
  have hA0 : 0<A 0 := by dsimp [A]; simp only [add_zero,sub_zero]; positivity
  have hd0 : 0<A 0*C 0-(μ*b/2)^2 := by
    simpa [A,C] using wellHessian_det_pos ha hab hμ hEL
  have he : ∀ᶠ t : ℝ in 𝓝 0,0<A t ∧ 0<A t*C t-(μ*b/2)^2 :=
    (hAc.eventually (eventually_gt_nhds hA0)).and
      (((hAc.mul hCc).sub continuousAt_const).eventually (eventually_gt_nhds hd0))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  have heps : ε/2∈Metric.ball (0:ℝ) ε := by
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    linarith
  obtain ⟨hAp,hdp⟩ := hball heps
  refine ⟨ε/2,half_pos hε,?_⟩
  intro x y
  have h := quadratic_nonneg (x:=x) (y:=y) hAp hdp.le
  dsimp [A,C] at h
  nlinarith

/-- Local quadratic growth at the ordered well; swapping coordinates gives the other well. -/
theorem scalarWell_local_growth {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ ρ κ : ℝ,0<ρ ∧ 0<κ ∧ ∀ u w : ℝ,
      (u-a)^2+(w-b)^2<ρ^2 →
      κ*((u-a)^2+(w-b)^2)≤scalarWell a b μ u w-scalarWell a b μ a b := by
  have hb : 0<b := ha.trans hab
  obtain ⟨δ,hδ,hquad⟩ := exists_wellHessian_margin ha hab hμ hEL
  let ρ := min δ (min (a/2) (b/2))
  have hρ : 0<ρ := lt_min hδ (lt_min (half_pos ha) (half_pos hb))
  have hρδ : ρ≤δ := min_le_left _ _
  have hρa : ρ≤a/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρb : ρ≤b/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,δ/2,hρ,half_pos hδ,?_⟩
  intro u w hnear
  have hau : |u-a|<ρ := by rw [abs_lt]; constructor <;> nlinarith [sq_nonneg (w-b)]
  have hbw : |w-b|<ρ := by rw [abs_lt]; constructor <;> nlinarith [sq_nonneg (u-a)]
  rw [abs_lt] at hau hbw
  have hu : 0<u := by linarith
  have hw : 0<w := by linarith
  have h1 := entropy_remainder_lower ha hu (show a≤a+δ by linarith) (show u≤a+δ by linarith)
  have h2 := entropy_remainder_lower hb hw (show b≤b+δ by linarith) (show w≤b+δ by linarith)
  have h3 := hquad (u-a) (w-b)
  have hE := balancedEL_wellCritical hEL
  rcases hE with ⟨hEa,hEb⟩
  have hid : scalarWell a b μ u w-scalarWell a b μ a b =
      (entropy u-entropy a-(u-a)*Real.log a)+(entropy w-entropy b-(w-b)*Real.log b)+
      μ*a/4*((u-a)^2+(w-b)^2)+μ*b/2*(u-a)*(w-b) := by
    unfold scalarWell
    linear_combination (u-a)*hEa+(w-b)*hEb
  rw [hid]
  have he1 : (u-a)^2/(2*(a+δ))=(1/(a+δ))*(u-a)^2/2 := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have he2 : (w-b)^2/(2*(b+δ))=(1/(b+δ))*(w-b)^2/2 := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [he1] at h1
  rw [he2] at h2
  nlinarith

/-- Squared Euclidean distance to the nearer of the two ordered wells. -/
def wellDistanceSq (a b u w : ℝ) : ℝ :=
  min ((u-a)^2+(w-b)^2) ((u-b)^2+(w-a)^2)

theorem wellDistanceSq_nonneg (a b u w : ℝ) : 0≤wellDistanceSq a b u w :=
  le_min (add_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem continuous_wellDistanceSq (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => wellDistanceSq a b p.1 p.2) := by unfold wellDistanceSq; fun_prop

theorem wellDistanceSq_le_two {a b u w : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1)
    (hu : u∈Icc 0 1) (hw : w∈Icc 0 1) : wellDistanceSq a b u w≤2 := by
  have h1 : (u-a)^2≤1 := by
    nlinarith [mul_nonneg (show 0≤1-(u-a) by linarith [hu.2,ha.1])
      (show 0≤1+(u-a) by linarith [hu.1,ha.2])]
  have h2 : (w-b)^2≤1 := by
    nlinarith [mul_nonneg (show 0≤1-(w-b) by linarith [hw.2,hb.1])
      (show 0≤1+(w-b) by linarith [hw.1,hb.2])]
  exact (min_le_left _ _).trans (by linarith)

/-- The scalar quadratic growth estimate `s6:growth`, with no unproved internal input. -/
theorem scalarWell_quadratic_growth {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ θ : ℝ,0<θ ∧ ∀ u∈Icc (0:ℝ) 1,∀ w∈Icc (0:ℝ) 1,
      θ*wellDistanceSq a b u w≤scalarWell a b μ u w-scalarWell a b μ a b := by
  obtain ⟨ρ,κ,hρ,hκ,hlocal⟩ := scalarWell_local_growth ha hab hμ hEL
  have hnear : ∀ u w : ℝ,wellDistanceSq a b u w<ρ^2 →
      κ*wellDistanceSq a b u w≤scalarWell a b μ u w-scalarWell a b μ a b := by
    intro u w h
    rcases min_lt_iff.mp h with h | h
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hκ.le).trans (hlocal u w h)
    · have hs : (w-a)^2+(u-b)^2<ρ^2 := by linarith
      have hl := hlocal w u hs
      rw [scalarWell_swap a b μ w u] at hl
      have hd : wellDistanceSq a b u w≤(w-a)^2+(u-b)^2 := by
        exact (min_le_right _ _).trans_eq (by ring)
      exact (mul_le_mul_of_nonneg_left hd hκ.le).trans hl
  let K : Set (ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ∩
    {p | ρ^2≤wellDistanceSq a b p.1 p.2}
  let gap := fun p : ℝ × ℝ => scalarWell a b μ p.1 p.2-scalarWell a b μ a b
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_wellDistanceSq a b))
  have hgap : Continuous gap := (continuous_scalarWell a b μ).sub continuous_const
  have hpos : ∀ p∈K,0<gap p := by
    intro p hp
    have hbase : 0≤gap p := sub_nonneg.mpr (scalarWell_min ha hab hb hμ hEL hp.1.1 hp.1.2)
    by_contra hn
    have he : scalarWell a b μ p.1 p.2=scalarWell a b μ a b := by
      have hz : gap p=0 := le_antisymm (le_of_not_gt hn) hbase
      exact sub_eq_zero.mp hz
    have hclass := (scalarWell_eq_min_iff ha hab hb hμ hEL hp.1.1 hp.1.2).mp he
    have hd : wellDistanceSq a b p.1 p.2=0 := by
      rcases hclass with h | h
      · simp [wellDistanceSq,h.1,h.2,add_nonneg (sq_nonneg (a-b)) (sq_nonneg (b-a))]
      · simp [wellDistanceSq,h.1,h.2,add_nonneg (sq_nonneg (b-a)) (sq_nonneg (a-b))]
    have hfar : ρ^2≤wellDistanceSq a b p.1 p.2 := hp.2
    rw [hd] at hfar
    nlinarith
  have hγ : ∃ γ : ℝ,0<γ ∧ ∀ p∈K,γ≤gap p := by
    by_cases hne : K.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne hgap.continuousOn
      exact ⟨gap p,hpos p hp,fun q hq => hmin hq⟩
    · exact ⟨1,by norm_num,fun p hp => False.elim (hne ⟨p,hp⟩)⟩
  obtain ⟨γ,hγ,hfar⟩ := hγ
  refine ⟨min κ (γ/2),lt_min hκ (half_pos hγ),?_⟩
  intro u hu w hw
  have hd0 := wellDistanceSq_nonneg a b u w
  by_cases hn : wellDistanceSq a b u w<ρ^2
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hd0).trans (hnear u w hn)
  · have hd2 := wellDistanceSq_le_two ⟨ha.le,(hab.trans hb).le⟩
      ⟨(ha.trans hab).le,hb.le⟩ hu hw
    have hm := hfar (u,w) ⟨⟨hu,hw⟩,le_of_not_gt hn⟩
    have ht := mul_le_mul_of_nonneg_right (min_le_right κ (γ/2)) hd0
    have ht' := mul_le_mul_of_nonneg_left hd2 (half_pos hγ).le
    dsimp [gap] at hm
    nlinarith

end SparseLowerTail.Section06
