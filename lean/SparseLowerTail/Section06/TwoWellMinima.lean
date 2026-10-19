import SparseLowerTail.Section06.TwoWell
import Mathlib.Topology.Order.IntermediateValue

/-! Global classification of the scalar insertion minima. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section04

def entropyQuadratic (A B x : ℝ) : ℝ := entropy x+A*x^2+B*x

theorem hasDerivAt_entropyQuadratic (A B : ℝ) {x : ℝ} (hx : x≠0) :
    HasDerivAt (entropyQuadratic A B) (Real.log x+2*A*x+B) x := by
  convert ((hasDerivAt_entropy hx).add (((hasDerivAt_id x).pow 2).const_mul A)).add
    ((hasDerivAt_id x).const_mul B) using 1
  simp
  ring

theorem continuous_entropyQuadratic (A B : ℝ) : Continuous (entropyQuadratic A B) := by
  exact (continuous_entropy.add (continuous_const.mul (continuous_id.pow 2))).add
    (continuous_const.mul continuous_id)

/-- Positive quadratic and nonnegative linear coefficients put a slice's minimum
strictly inside the unit interval, where the usual stationary equation holds. -/
theorem entropyQuadratic_min_stationary {A B x : ℝ} (hA : 0<A) (hB : 0≤B)
    (hx : x∈Icc 0 1) (hmin : IsMinOn (entropyQuadratic A B) (Icc 0 1) x) :
    x∈Ioo 0 1 ∧ Real.log x+2*A*x+B=0 := by
  let ε := Real.exp (-2*A-B-1)
  have hε : 0<ε := Real.exp_pos _
  have hε1 : ε<1 := by dsimp [ε]; rw [Real.exp_lt_one_iff]; linarith
  let d := fun t : ℝ => Real.log t+2*A*t+B
  have hdε : d ε<0 := by
    have he : Real.log ε=-2*A-B-1 := Real.log_exp _
    dsimp [d]
    rw [he]
    nlinarith
  have hd1 : 0<d 1 := by dsimp [d]; simp; linarith
  have hdc : ContinuousOn d (Icc ε 1) := by
    intro t ht
    have ht0 : t≠0 := ne_of_gt (hε.trans_le ht.1)
    apply ContinuousAt.continuousWithinAt
    exact ((Real.continuousAt_log ht0).add (continuousAt_const.mul continuousAt_id)).add
      continuousAt_const
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc hε1.le hdc ⟨hdε.le,hd1.le⟩
  have hs0 : 0<s := hε.trans_le hs.1
  have hs1 : s<1 := by
    by_contra hn
    have : s=1 := le_antisymm hs.2 (le_of_not_gt hn)
    subst s
    linarith
  have hdm : StrictMonoOn d (Ioi 0) := by
    intro u hu v hv huv
    dsimp [d]
    have := Real.strictMonoOn_log hu hv huv
    nlinarith
  have hanti : StrictAntiOn (entropyQuadratic A B) (Icc 0 s) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 s) (continuous_entropyQuadratic A B).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_entropyQuadratic A B ht.1.ne').deriv]
    exact lt_of_lt_of_eq (hdm ht.1 hs0 ht.2) he
  have hmono : StrictMonoOn (entropyQuadratic A B) (Icc s 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc s 1) (continuous_entropyQuadratic A B).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_entropyQuadratic A B (ne_of_gt (hs0.trans ht.1))).deriv]
    exact lt_of_eq_of_lt he.symm (hdm hs0 (hs0.trans ht.1) ht.1)
  have hxs : x=s := by
    rcases lt_trichotomy x s with h | h | h
    · have := hanti ⟨hx.1,h.le⟩ ⟨hs0.le,le_rfl⟩ h
      exact False.elim ((not_lt_of_ge (hmin ⟨hs0.le,hs1.le⟩)) this)
    · exact h
    · have := hmono ⟨le_rfl,hs1.le⟩ ⟨h.le,hx.2⟩ h
      exact False.elim ((not_lt_of_ge (hmin ⟨hs0.le,hs1.le⟩)) this)
  subst x
  exact ⟨⟨hs0,hs1⟩,he⟩

/-- A global minimum of the scalar insertion problem is an interior critical point. -/
theorem scalarWell_min_critical {a b μ u w : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hu : u∈Icc 0 1) (hw : w∈Icc 0 1)
    (hmin : ∀ v∈Icc (0:ℝ) 1,∀ z∈Icc (0:ℝ) 1,
      scalarWell a b μ u w≤scalarWell a b μ v z) :
    u∈Ioo 0 1 ∧ w∈Ioo 0 1 ∧ WellCritical (μ*a/2) (μ*b/2) u w := by
  have hb : 0<b := ha.trans hab
  have hA : 0<μ*a/4 := by positivity
  have hu0 := hu.1
  have hw0 := hw.1
  have hBu : 0≤μ*b*w/2 := by positivity
  have hBw : 0≤μ*b*u/2 := by positivity
  have hminu : IsMinOn (entropyQuadratic (μ*a/4) (μ*b*w/2)) (Icc 0 1) u := by
    intro v hv
    have := hmin v hv w hw
    dsimp [scalarWell,entropyQuadratic] at *
    nlinarith
  have hminw : IsMinOn (entropyQuadratic (μ*a/4) (μ*b*u/2)) (Icc 0 1) w := by
    intro z hz
    have := hmin u hu z hz
    dsimp [scalarWell,entropyQuadratic] at *
    nlinarith
  obtain ⟨hui,hue⟩ := entropyQuadratic_min_stationary hA hBu hu hminu
  obtain ⟨hwi,hwe⟩ := entropyQuadratic_min_stationary hA hBw hw hminw
  exact ⟨hui,hwi,by constructor <;> nlinarith⟩

def transverseSlope (s c t : ℝ) : ℝ :=
  Real.log (s+t)-Real.log (s-t)-2*c*t

theorem hasDerivAt_transverseSlope (c : ℝ) {s t : ℝ} (hp : s+t≠0) (hm : s-t≠0) :
    HasDerivAt (transverseSlope s c) (1/(s+t)+1/(s-t)-2*c) t := by
  have hi := hasDerivAt_id t
  convert (((Real.hasDerivAt_log hp).comp t (hi.const_add s)).sub
    ((Real.hasDerivAt_log hm).comp t (hi.const_sub s))).sub (hi.const_mul (2*c)) using 1
  simp

theorem hasDerivAt_scalarWell_transverse (a b μ : ℝ) {s t : ℝ}
    (hp : s+t≠0) (hm : s-t≠0) :
    HasDerivAt (fun x => scalarWell a b μ (s+x) (s-x))
      (transverseSlope s (μ*b/2-μ*a/2) t) t := by
  have hi := hasDerivAt_id t
  have hh := ((hasDerivAt_entropy hp).comp t (hi.const_add s)).add
    ((hasDerivAt_entropy hm).comp t (hi.const_sub s))
  have hpoly := (((hi.pow 2).const_mul (a-b)).const_add ((a+b)*s^2)).const_mul (μ/2)
  convert hh.add hpoly using 1
  · funext x
    unfold scalarWell
    simp only [Pi.add_apply,Function.comp_apply,Pi.pow_apply,id_eq]
    ring
  · unfold transverseSlope
    simp
    ring

/-- Negative transverse curvature supplies an explicit nearby improving direction. -/
theorem exists_transverse_improvement {a b μ s : ℝ} (hs : s∈Ioo 0 1)
    (hcurv : 1/s-(μ*b/2-μ*a/2)<0) :
    ∃ t : ℝ,0<t ∧ s+t∈Icc 0 1 ∧ s-t∈Icc 0 1 ∧
      scalarWell a b μ (s+t) (s-t)<scalarWell a b μ s s := by
  let c := μ*b/2-μ*a/2
  let g := transverseSlope s c
  let f := fun t => scalarWell a b μ (s+t) (s-t)
  have hcont : ContinuousAt (fun t : ℝ => 1/(s+t)+1/(s-t)-2*c) 0 := by
    fun_prop (disch := simpa using hs.1.ne')
  have hneg0 : 1/(s+0)+1/(s-0)-2*c<0 := by
    dsimp [c]
    simp only [add_zero,sub_zero]
    linarith
  have he : ∀ᶠ t : ℝ in 𝓝 0,1/(s+t)+1/(s-t)-2*c<0 :=
    hcont.eventually (eventually_lt_nhds hneg0)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp he
  let δ := min (ε/2) (min (s/2) ((1-s)/2))
  have hδ : 0<δ := by dsimp [δ]; exact lt_min (half_pos hε) (lt_min (half_pos hs.1) (half_pos (sub_pos.mpr hs.2)))
  have hδε : δ≤ε/2 := min_le_left _ _
  have hδs : δ≤s/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ≤(1-s)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbounds : ∀ t∈Icc (0:ℝ) δ,0<s+t ∧ s+t<1 ∧ 0<s-t ∧ s-t<1 := by
    intro t ht
    constructor
    · linarith [hs.1,ht.1]
    constructor
    · linarith [ht.2,hs.2]
    constructor <;> linarith [ht.1,ht.2,hs.1,hs.2]
  have hganti : StrictAntiOn g (Icc 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 δ)
    · intro t ht
      exact (hasDerivAt_transverseSlope c (hbounds t ht).1.ne'
        (hbounds t ht).2.2.1.ne').continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t∈Icc (0:ℝ) δ := ⟨ht.1.le,ht.2.le⟩
      rw [(hasDerivAt_transverseSlope c (hbounds t ht').1.ne'
        (hbounds t ht').2.2.1.ne').deriv]
      apply hball
      simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1]
      linarith [ht.2]
  have hfanti : StrictAntiOn f (Icc 0 δ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 δ)
    · intro t ht
      exact (hasDerivAt_scalarWell_transverse a b μ (hbounds t ht).1.ne'
        (hbounds t ht).2.2.1.ne').continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : t∈Icc (0:ℝ) δ := ⟨ht.1.le,ht.2.le⟩
      rw [(hasDerivAt_scalarWell_transverse a b μ (hbounds t ht').1.ne'
        (hbounds t ht').2.2.1.ne').deriv]
      have h := hganti ⟨le_rfl,hδ.le⟩ ht' ht.1
      simpa [g,transverseSlope] using h
  refine ⟨δ,hδ,⟨(hbounds δ ⟨hδ.le,le_rfl⟩).1.le,(hbounds δ ⟨hδ.le,le_rfl⟩).2.1.le⟩,
    ⟨(hbounds δ ⟨hδ.le,le_rfl⟩).2.2.1.le,(hbounds δ ⟨hδ.le,le_rfl⟩).2.2.2.le⟩,?_⟩
  simpa [f] using hfanti ⟨le_rfl,hδ.le⟩ ⟨hδ.le,le_rfl⟩ hδ

/-- Global scalar minimizers can only be the two off-diagonal wells. -/
theorem scalarWell_min_classification {a b μ u w : ℝ} (ha : 0<a) (hab : a<b)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) (hu : u∈Icc 0 1) (hw : w∈Icc 0 1)
    (hmin : ∀ v∈Icc (0:ℝ) 1,∀ z∈Icc (0:ℝ) 1,
      scalarWell a b μ u w≤scalarWell a b μ v z) :
    (u=a ∧ w=b) ∨ (u=b ∧ w=a) := by
  obtain ⟨hui,hwi,hcrit⟩ := scalarWell_min_critical ha hab hμ hu hw hmin
  rcases wellCritical_classification ha hab hμ hEL hui.1 hwi.1 hcrit with he | h | h
  · subst w
    have hc := diagonal_critical_curvature_neg ha hab hμ hEL hui.1 hcrit
    obtain ⟨t,_,hp,hm,hlt⟩ := exists_transverse_improvement hui hc
    exact False.elim ((not_lt_of_ge (hmin _ hp _ hm)) hlt)
  · exact Or.inl h
  · exact Or.inr h

theorem continuous_scalarWell (a b μ : ℝ) :
    Continuous (fun p : ℝ × ℝ => scalarWell a b μ p.1 p.2) := by
  have h1 := continuous_entropy.comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have h2 := continuous_entropy.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))
  unfold scalarWell
  fun_prop

/-- The two known wells are the global minima on the whole compact square. -/
theorem scalarWell_min {a b μ : ℝ} (ha : 0<a) (hab : a<b) (_hb : b<1)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) {u w : ℝ}
    (hu : u∈Icc 0 1) (hw : w∈Icc 0 1) :
    scalarWell a b μ a b≤scalarWell a b μ u w := by
  let S : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hne : S.Nonempty := ⟨(0,0),by simp [S]⟩
  obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne (continuous_scalarWell a b μ).continuousOn
  have hpm : ∀ v∈Icc (0:ℝ) 1,∀ z∈Icc (0:ℝ) 1,
      scalarWell a b μ p.1 p.2≤scalarWell a b μ v z := fun v hv z hz => hmin (a := (v,z)) ⟨hv,hz⟩
  rcases scalarWell_min_classification ha hab hμ hEL hp.1 hp.2 hpm with h | h
  · simpa only [h.1,h.2] using hpm u hu w hw
  · simpa only [h.1,h.2,scalarWell_swap a b μ b a] using hpm u hu w hw

/-- Equality at the minimum occurs precisely at the two EL wells. -/
theorem scalarWell_eq_min_iff {a b μ : ℝ} (ha : 0<a) (hab : a<b) (hb : b<1)
    (hμ : 0<μ) (hEL : BalancedEL a b μ) {u w : ℝ}
    (hu : u∈Icc 0 1) (hw : w∈Icc 0 1) :
    scalarWell a b μ u w=scalarWell a b μ a b ↔
      (u=a ∧ w=b) ∨ (u=b ∧ w=a) := by
  constructor
  · intro he
    apply scalarWell_min_classification ha hab hμ hEL hu hw
    intro v hv z hz
    rw [he]
    exact scalarWell_min ha hab hb hμ hEL hv hz
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact scalarWell_swap _ _ _ _ _

end SparseLowerTail.Section06
