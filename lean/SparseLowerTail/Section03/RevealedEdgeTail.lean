import SparseLowerTail.Section03.RevealedHarris
import SparseLowerTail.Section03.BernoulliConcentration

/-! Exponential control of the number of present revealed edges under lower-tail conditioning. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def revealedEdgeCount (W : Finset ι) (z : ι → Bool) : ℝ := ∑ i∈W, (z i).toNat

omit [Fintype ι] [DecidableEq ι] in
/-- The exact revealed-edge count is increasing. -/
theorem revealedEdgeCount_monotone (W : Finset ι) : Monotone (revealedEdgeCount W) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast Bool.toNat_le_toNat (hxy i)

/-- The original product law has exponential moment at most exp(2p|W|). -/
theorem revealedEdgeCount_product_exp_moment (W : Finset ι) {p : ℝ} (hp : p∈Icc (0:ℝ) 1) :
    (∑ z, productBernoulliMass (fun _ : ι => p) z*Real.exp (revealedEdgeCount W z))≤
      Real.exp (2*p*W.card) := by
  let c : ι → ℝ := fun i => if i∈W then 1 else 0
  have hN : ∀ z : ι → Bool, revealedEdgeCount W z=
      bernoulliCenteredSum (fun _ : ι => p) c z+p*W.card := by
    intro z
    simp only [bernoulliCenteredSum,c,ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,
      Finset.univ_inter,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,revealedEdgeCount]
    ring
  have hcenter : (∑ z, productBernoulliMass (fun _ : ι => p) z*
      Real.exp (bernoulliCenteredSum (fun _ : ι => p) c z))≤Real.exp (p*W.card) := by
    have he := productBernoulli_exp_moment (fun _ : ι => p) c 1
    simp only [one_mul] at he
    rw [he]
    calc
      _≤∏ i, Real.exp (if i∈W then p else 0) := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg (fun b _ => mul_nonneg (bernoulliMass_nonneg hp b) (Real.exp_pos _).le)
        · intro i _
          by_cases hi : i∈W
          · simpa only [c,if_pos hi,one_mul,one_pow,mul_one] using
              bernoulli_exp_moment_le hp (by norm_num : |(1:ℝ)|≤1)
          · simp [c,hi,bernoulliMass]
      _=Real.exp (p*W.card) := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
        congr 1; ring
  simp_rw [hN,Real.exp_add,← mul_assoc]
  rw [← Finset.sum_mul]
  calc
    _≤Real.exp (p*W.card)*Real.exp (p*W.card) := mul_le_mul_of_nonneg_right hcenter (Real.exp_pos _).le
    _=Real.exp (2*p*W.card) := by rw [← Real.exp_add]; congr 1; ring

/-- A small revealed set has the required exponentially small upper tail under the original product law. -/
theorem revealedEdgeCount_product_tail (W : Finset ι) {p α N : ℝ} (hp : p∈Icc (0:ℝ) 1)
    (hW : (W.card:ℝ)≤α*N/2) :
    finiteEventMass (productBernoulliMass (fun _ : ι => p))
      (Finset.univ.filter (fun z => 2*α*p*N<revealedEdgeCount W z))≤Real.exp (-α*p*N) := by
  have hm := finite_exp_markov (productBernoulliMass (fun _ : ι => p)) (revealedEdgeCount W)
    (fun z => finiteProductMass_nonneg _ (fun _ b => bernoulliMass_nonneg hp b) z)
    (t:=1) (a:=2*α*p*N) (by norm_num)
  simp only [one_mul,neg_one_mul] at hm
  calc
    _≤Real.exp (-(2*α*p*N))*Real.exp (2*p*W.card) :=
      hm.trans (mul_le_mul_of_nonneg_left (revealedEdgeCount_product_exp_moment W hp) (Real.exp_pos _).le)
    _=Real.exp (-(2*α*p*N)+2*p*W.card) := by rw [← Real.exp_add]
    _≤_ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hW hp.1])

/-- Harris suppression transfers the revealed-edge tail to the actual lower-tail conditioned law. -/
theorem revealedEdgeCount_conditioned_tail (H : Finset (Finset ι)) (r : ℕ) (hr : 1≤r)
    (hH : ∀ A∈H, A.card=r) {p η α N : ℝ} (hp : p∈Ioo (0:ℝ) 1) (hη : 0≤η)
    (hHarris : ClassicalHarrisPositiveAssociation ι) (W : Finset ι) (hW : (W.card:ℝ)≤α*N/2) :
    finiteEventMass (hypergraphLowerLaw H r p η)
      (Finset.univ.filter (fun z => 2*α*p*N<revealedEdgeCount W z))≤Real.exp (-α*p*N) := by
  have hupper : IsUpperSet ((Finset.univ.filter (fun z => 2*α*p*N<revealedEdgeCount W z) : Finset (ι → Bool)) : Set (ι → Bool)) := by
    intro x y hxy hx
    change y∈Finset.univ.filter (fun z => 2*α*p*N<revealedEdgeCount W z)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hx).2.trans_le (revealedEdgeCount_monotone W hxy)⟩
  exact (harris_conditioned_event_le hHarris (fun _ => p) (fun _ => ⟨hp.1.le,hp.2.le⟩) _
    (hypergraphLowerEvent H r p η) hupper (hypergraphLowerEvent_isLowerSet H r p η)
    (hypergraphLowerEvent_probability_pos H r hr hH hp hη)).trans (revealedEdgeCount_product_tail W ⟨hp.1.le,hp.2.le⟩ hW)

end SparseLowerTail.Section03
