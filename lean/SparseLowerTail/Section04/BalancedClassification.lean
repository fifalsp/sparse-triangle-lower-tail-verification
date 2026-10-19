import SparseLowerTail.BalancedExistence
import SparseLowerTail.Section04.Ray

/-!
# From the cost gap to balanced optimizer classification

This is the reduction in `cor:Vbal`: actual minimizers of the constrained
balanced problem are characterized from the scalar gap comparison in
`thm:crossing`. The scalar comparison is an explicit input here and will be
instantiated by the crossing theorem, rather than assumed as an external fact.
-/
noncomputable section
open Set
namespace SparseLowerTail.Section04

/-- A lower bound for every normalized ray gives a lower bound for every
feasible pair, including pairs with inactive constraint or reversed ordering. -/
theorem balancedCost_lower_of_rayGap_lower {r w : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hw : w ≤ 0) (hgap : ∀ z ∈ Ioo (0 : ℝ) 1, w ≤ rayGap r z)
    {a b : ℝ} (hf : BalancedFeasible r a b) :
    entropy r + r*w ≤ balancedCost a b := by
  by_cases hab : b ≤ a
  · have he := entropy_target_le_balancedCost ⟨hr.1.le, hr.2.le⟩ hf hab
    have hm : r*w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.1.le hw
    linarith
  · obtain ⟨c, d, hcd, hlt, ht, hcost, _⟩ :=
      exists_saturated_pair hr hf (lt_of_not_ge hab)
    obtain ⟨_, hz, hz1, ha, hb⟩ := saturated_pair_ray hcd.1.1 hlt hr.1 ht
    have he : balancedCost c d = entropy r + r*rayGap r (c/d) := by
      exact (congrArg₂ balancedCost ha hb).trans (scaled_ray_cost hz hr.1)
    have hle := mul_le_mul_of_nonneg_left (hgap (c/d) ⟨hz, hz1⟩) hr.1.le
    linarith

/-- Positivity of all open-ray gaps forces the constant pair to be the only
balanced minimizer. -/
theorem balancedMinimizer_iff_diagonal_of_gap_pos {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hgap : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < rayGap r z) (a b : ℝ) :
    IsBalancedMinimizer r a b ↔ a = r ∧ b = r := by
  constructor
  · intro hm
    rcases balancedMinimizer_diagonal_or_saturated hr hm with he | ⟨hab, ht⟩
    · exact he
    · obtain ⟨_, hz, hz1, ha, hb⟩ := saturated_pair_ray hm.1.1.1 hab hr.1 ht
      have he : balancedCost a b = entropy r + r*rayGap r (a/b) := by
        exact (congrArg₂ balancedCost ha hb).trans (scaled_ray_cost hz hr.1)
      have hc := hm.2 r r (balanced_diagonal_feasible ⟨hr.1.le, hr.2.le⟩)
      have hp := mul_pos hr.1 (hgap (a/b) ⟨hz, hz1⟩)
      simp only [balancedCost_diagonal] at hc
      linarith
  · rintro ⟨rfl, rfl⟩
    refine ⟨balanced_diagonal_feasible ⟨hr.1.le, hr.2.le⟩, ?_⟩
    intro c d hcd
    simpa using balancedCost_lower_of_rayGap_lower hr (le_refl (0 : ℝ))
      (fun z hz => (hgap z hz).le) hcd

/-- Consequence for the balanced variational value in the constant phase. -/
theorem balancedValue_eq_entropy_of_gap_pos {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hgap : ∀ z ∈ Ioo (0 : ℝ) 1, 0 < rayGap r z) :
    balancedValue r = entropy r := by
  have hm := (balancedMinimizer_iff_diagonal_of_gap_pos hr hgap r r).mpr ⟨rfl,rfl⟩
  simpa using (isBalancedMinimizer_iff.mp hm).2.symm

/-- A branch point with triangle target r is a feasible balanced pair. -/
theorem branch_pair_feasible {r z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1)
    (hinv : branchRho z = r) : BalancedFeasible r (branchA z) (branchB z) := by
  have hs := branch_spec hz.1 hz.2
  have ht : balancedTriangle (branchA z) (branchB z) = r^3 := by
    rw [branch_eq_scaled_ray hz.1 |>.1, branch_eq_scaled_ray hz.1 |>.2,
      scaled_ray_triangle hz.1, hinv]
  exact ⟨⟨hs.1.le, (hs.2.1.trans hs.2.2.1).le⟩, ⟨(branchB_pos z).le, hs.2.2.1.le⟩, ht.le⟩

/-- The candidate cost expressed through the gap at its own branch parameter. -/
theorem branch_cost_eq_gap {r z : ℝ} (hr : 0 < r) (hz : 0 < z)
    (hinv : branchRho z = r) :
    balancedCost (branchA z) (branchB z) = entropy r + r*rayGap r z := by
  obtain ⟨ha, hb⟩ := branch_eq_scaled_ray hz
  rw [hinv] at ha hb
  rw [ha, hb]
  exact scaled_ray_cost hz hr

/-- A nonpositive, uniquely minimizing gap produces exactly the balanced
branch pair, and also the diagonal pair precisely when the gap equals zero. -/
theorem balancedMinimizer_iff_of_unique_gap_min {r z : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1)
    (hinv : branchRho z = r) (hn : rayGap r z ≤ 0)
    (hgap : ∀ w ∈ Ioo (0 : ℝ) 1,
      rayGap r z ≤ rayGap r w ∧ (rayGap r w = rayGap r z ↔ w = z)) (a b : ℝ) :
    IsBalancedMinimizer r a b ↔
      (a = branchA z ∧ b = branchB z) ∨ (a = r ∧ b = r ∧ rayGap r z = 0) := by
  have hf := branch_pair_feasible hz hinv
  have he := branch_cost_eq_gap hr.1 hz.1 hinv
  have hm : IsBalancedMinimizer r (branchA z) (branchB z) := by
    refine ⟨hf, ?_⟩
    intro c d hcd
    rw [he]
    exact balancedCost_lower_of_rayGap_lower hr hn (fun w hw => (hgap w hw).1) hcd
  constructor
  · intro hab
    rcases balancedMinimizer_diagonal_or_saturated hr hab with ⟨rfl,rfl⟩ | ⟨hlt,ht⟩
    · right
      refine ⟨rfl,rfl,?_⟩
      have hle := hab.2 _ _ hf
      simp only [balancedCost_diagonal] at hle
      rw [he] at hle
      nlinarith [hr.1]
    · left
      obtain ⟨_, hw, hw1, ha, hb⟩ := saturated_pair_ray hab.1.1.1 hlt hr.1 ht
      have hew : balancedCost a b = entropy r + r*rayGap r (a/b) := by
        exact (congrArg₂ balancedCost ha hb).trans (scaled_ray_cost hw hr.1)
      have hcost : balancedCost a b = balancedCost (branchA z) (branchB z) :=
        le_antisymm (hab.2 _ _ hf) (hm.2 _ _ hab.1)
      rw [hew, he] at hcost
      have hze : a/b = z := (hgap (a/b) ⟨hw,hw1⟩).2.mp
        (mul_left_cancel₀ (ne_of_gt hr.1) (add_left_cancel hcost))
      obtain ⟨hA,hB⟩ := branch_eq_scaled_ray hz.1
      rw [hinv] at hA hB
      rw [hze] at ha hb
      exact ⟨ha.trans hA.symm, hb.trans hB.symm⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl,hzero⟩)
    · exact hm
    · refine ⟨balanced_diagonal_feasible ⟨hr.1.le,hr.2.le⟩, ?_⟩
      intro c d hcd
      have hc := hm.2 c d hcd
      simpa [he,hzero] using hc

/-- The balanced value once the nonpositive global gap minimum is established. -/
theorem balancedValue_eq_branch_of_unique_gap_min {r z : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1)
    (hinv : branchRho z = r) (hn : rayGap r z ≤ 0)
    (hgap : ∀ w ∈ Ioo (0 : ℝ) 1,
      rayGap r z ≤ rayGap r w ∧ (rayGap r w = rayGap r z ↔ w = z)) :
    balancedValue r = balancedCost (branchA z) (branchB z) := by
  have hm := (balancedMinimizer_iff_of_unique_gap_min hr hz hinv hn hgap _ _).mpr
    (Or.inl ⟨rfl,rfl⟩)
  exact (isBalancedMinimizer_iff.mp hm).2.symm

/-- The strict order of the two branch values around their triangle target,
recorded in `s4:eq:arbr`. -/
theorem branch_pair_target_bounds {r z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1)
    (hinv : branchRho z = r) :
    0 < branchA z ∧ branchA z < r ∧ r < branchB z ∧ branchB z < 1 := by
  have ha := branchA_pos hz.1
  have hb := branchB_pos z
  have hab := branchA_lt_branchB hz.2
  have hdiff : 0 < branchB z - branchA z := sub_pos.mpr hab
  have hlo : 0 < 3*branchA z*(branchB z-branchA z)*(branchB z+branchA z) := by positivity
  have hup : 0 < (branchB z-branchA z)*
      (branchA z^2+branchA z*branchB z+4*branchB z^2) := by positivity
  have ht : balancedTriangle (branchA z) (branchB z) = r^3 := by
    obtain ⟨hA,hB⟩ := branch_eq_scaled_ray hz.1
    rw [hA,hB,scaled_ray_triangle hz.1,hinv]
  unfold balancedTriangle at ht
  have hl : branchA z^3 < r^3 := by nlinarith
  have hu : r^3 < branchB z^3 := by nlinarith
  exact ⟨ha, (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp hl,
    (show Odd (3 : ℕ) by decide).strictMono_pow.lt_iff_lt.mp hu, branchB_lt_one hz.1 hz.2⟩

/-- Identification with the supremum definition of the threshold, once the
balanced strict-improvement interval has been proved. -/
theorem threshold_eq_of_balanced_improvement {rstar : ℝ}
    (hrstar : rstar ∈ Ioo (0 : ℝ) 1)
    (himprove : ∀ r ∈ Ioo (0 : ℝ) 1, balancedValue r < entropy r ↔ r < rstar) :
    threshold = rstar := by
  have hs : {r | r ∈ Ioo (0 : ℝ) 1 ∧ balancedValue r < entropy r} = Ioo 0 rstar := by
    ext r
    constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr.1, (himprove r hr).mp h⟩
    · intro hr
      have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1,hr.2.trans hrstar.2⟩
      exact ⟨hr1,(himprove r hr1).mpr hr.2⟩
  rw [threshold,hs,csSup_Ioo hrstar.1]

end SparseLowerTail.Section04
