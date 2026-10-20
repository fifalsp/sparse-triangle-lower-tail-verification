import SparseLowerTail.Section03.LowerTailRate
import SparseLowerTail.Section03.FiniteProbabilityBounds

/-! Value and entropy estimates used in the conditioned-structure good-event proof. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
open Section02

/-- Quantitative baseline estimate s3:v0, with exactly the stated small-error conditions. -/
theorem conditional_value_baseline_bounds {r s α ω : ℝ} (n : ℕ)
    (hr : 0<r) (hrs : r≤s) (hs : s≤1) (hα : 0≤α)
    (hscale : 1-r/s≤ω/8) (hn : 1/(n:ℝ)≤ω/8) (hαsmall : α≤ω/8) :
    let v₀ := value s-1/(n:ℝ)-2*α
    0≤value r-v₀ ∧ value r-v₀≤ω/2 ∧ v₀≤1 := by
  have hg := value_difference_bounds hr hrs hs
  have hinv : (0:ℝ)≤1/(n:ℝ) := by positivity
  have hv : value s≤1 := (value_le_entropy ⟨hr.le.trans hrs,hs⟩).trans
    (entropy_le_one ⟨hr.le.trans hrs,hs⟩)
  dsimp
  constructor
  · linarith [hg.1]
  · constructor <;> linarith [hg.2]

/-- The positive cost excess and the dependence entropy are both small in mean.
The quantities X and D are normalized by n²p/2 before this lemma is applied. -/
theorem conditional_excess_and_dependence_means {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ X D : ι → ℝ) (hμ : ∀ y, 0≤μ y) (hμsum : ∑ y, μ y=1)
    (hX : ∀ y, 0≤X y) (hD : ∀ y, 0≤D y) (G : Finset ι)
    {V v₀ ζ ω : ℝ} (hv₀ : v₀≤1) (hG : ∀ y∈G, v₀≤X y)
    (hbudget : (∑ y, μ y*D y)+(∑ y, μ y*X y)≤V+ζ)
    (hgap : V-v₀≤ω/2) (hζ : ζ≤ω/8)
    (hbad : finiteEventMass μ Gᶜ≤ω/8) :
    (∑ y, μ y*max (X y-v₀) 0)≤ω ∧ (∑ y, μ y*D y)≤ω := by
  have hbadnonneg : 0≤finiteEventMass μ Gᶜ := Finset.sum_nonneg (fun y _ => hμ y)
  have hω : 0≤ω := by linarith
  have hDnonneg : 0≤∑ y, μ y*D y := Finset.sum_nonneg (fun y _ => mul_nonneg (hμ y) (hD y))
  have hexcess := finite_excess_mean_le μ X hμ hμsum hX G hv₀ hG
  have hdepend := finite_dependence_mean_le μ X D hμ hμsum hX G hv₀ hG hbudget
  constructor <;> linarith

/-- Markov's bound for the excessive-cost event G₂ᶜ. -/
theorem conditional_excess_cost_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ X : ι → ℝ) (hμ : ∀ y, 0≤μ y) {v₀ γ ω : ℝ} (hγ : 0<γ)
    (hmean : (∑ y, μ y*max (X y-v₀) 0)≤ω) :
    finiteEventMass μ (Finset.univ.filter (fun y => v₀+γ<X y))≤ω/γ := by
  have hmarkov := finite_event_markov μ (fun y => max (X y-v₀) 0) hμ
    (fun y => le_max_right _ _) (Finset.univ.filter (fun y => v₀+γ<X y)) hγ
    (fun y hy => (show γ≤X y-v₀ by linarith [(Finset.mem_filter.mp hy).2]).trans (le_max_left _ _))
  exact hmarkov.trans (div_le_div_of_nonneg_right hmean hγ.le)

end SparseLowerTail.Section03
