import SparseLowerTail.Section03.HarrisConditioning
import Mathlib.Analysis.Complex.Exponential

/-! Finite Bernoulli exponential moments and the cut-test concentration bound. -/
noncomputable section
open Set
open scoped BigOperators
namespace SparseLowerTail.Section03

def bernoulliCenteredSum {ι : Type*} [Fintype ι] (q c : ι → ℝ)
    (z : ι → Bool) : ℝ := ∑ i, c i*((z i).toNat-q i)

theorem bernoulliMass_nonneg {q : ℝ} (hq : q∈Icc (0:ℝ) 1) (b : Bool) :
    0≤bernoulliMass q b := by cases b <;> simp [bernoulliMass] <;> linarith [hq.1,hq.2]

/-- Exact exponential moment of one centered Bernoulli variable. -/
theorem bernoulli_exp_moment (q t : ℝ) :
    (∑ b : Bool, bernoulliMass q b*Real.exp (t*(b.toNat-q))) =
      Real.exp (-t*q)*(1-q+q*Real.exp t) := by
  simp only [Fintype.sum_bool, bernoulliMass, Bool.toNat_false, Bool.toNat_true,
    Nat.cast_zero, Nat.cast_one, zero_sub, mul_neg]
  rw [show t*(1-q)=t+(-t*q) by ring, Real.exp_add]
  ring_nf

/-- The scalar estimate used in the manuscript, valid for both signs of t. -/
theorem bernoulli_exp_moment_le {q t : ℝ} (hq : q∈Icc (0:ℝ) 1) (ht : |t|≤1) :
    (∑ b : Bool, bernoulliMass q b*Real.exp (t*(b.toNat-q))) ≤ Real.exp (q*t^2) := by
  rw [bernoulli_exp_moment]
  have hlinear : 1-q+q*Real.exp t ≤ Real.exp (q*(Real.exp t-1)) := by
    nlinarith [Real.add_one_le_exp (q*(Real.exp t-1))]
  have hrem : Real.exp t-1-t ≤ t^2 :=
    (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le ht)
  calc
    _ ≤ Real.exp (-t*q)*Real.exp (q*(Real.exp t-1)) :=
      mul_le_mul_of_nonneg_left hlinear (Real.exp_pos _).le
    _ = Real.exp (q*(Real.exp t-1-t)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrem hq.1)

/-- Independence is an exact finite product identity. -/
theorem productBernoulli_exp_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q c : ι → ℝ) (t : ℝ) :
    (∑ z, productBernoulliMass q z*Real.exp (t*bernoulliCenteredSum q c z)) =
      ∏ i, ∑ b : Bool, bernoulliMass (q i) b*Real.exp (t*c i*(b.toNat-q i)) := by
  simp only [bernoulliCenteredSum, Finset.mul_sum, Real.exp_sum,
    productBernoulliMass, finiteProductMass, ← Finset.prod_mul_distrib, mul_assoc]
  exact (Fintype.prod_sum (fun i (b : Bool) =>
    bernoulliMass (q i) b*Real.exp (t*(c i*(b.toNat-q i))))).symm

/-- Uniform coefficients of absolute value at most two give the factor four. -/
theorem productBernoulli_exp_moment_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q c : ι → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) 1)
    (hc : ∀ i, |c i|≤2) {t : ℝ} (ht : |t|≤1/2) :
    (∑ z, productBernoulliMass q z*Real.exp (t*bernoulliCenteredSum q c z)) ≤
      Real.exp (4*t^2*∑ i, q i) := by
  rw [productBernoulli_exp_moment]
  calc
    _ ≤ ∏ i, Real.exp (4*t^2*q i) := by
      apply Finset.prod_le_prod
      · intro i _; exact Finset.sum_nonneg (fun b _ => mul_nonneg
          (bernoulliMass_nonneg (hq i) b) (Real.exp_pos _).le)
      · intro i _
        have hit : |t*c i|≤1 := by
          rw [abs_mul]
          nlinarith [abs_nonneg t,abs_nonneg (c i),hc i]
        have hs := bernoulli_exp_moment_le (hq i) hit
        have hcs : (c i)^2≤4 := by nlinarith [sq_abs (c i),hc i,abs_nonneg (c i)]
        exact hs.trans (Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg (hq i).1 (sq_nonneg t),
            mul_nonneg (mul_nonneg (hq i).1 (sq_nonneg t)) (sub_nonneg.mpr hcs)]))
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- Finite exponential Markov inequality, proved directly by summation. -/
theorem finite_exp_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (m X : Ω → ℝ) (hm : ∀ z, 0≤m z) {t a : ℝ} (ht : 0≤t) :
    finiteEventMass m (Finset.univ.filter (fun z => a<X z)) ≤
      Real.exp (-t*a)*(∑ z, m z*Real.exp (t*X z)) := by
  let E := Finset.univ.filter (fun z => a<X z)
  have he : finiteEventMass m E*Real.exp (t*a) ≤ ∑ z, m z*Real.exp (t*X z) := by
    calc
      _ = ∑ z∈E, m z*Real.exp (t*a) := by rw [finiteEventMass, Finset.sum_mul]
      _ ≤ ∑ z∈E, m z*Real.exp (t*X z) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hz).2.le ht)) (hm z)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun z _ _ => mul_nonneg (hm z) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (-t*a)).le
  have hi : Real.exp (-t*a)*Real.exp (t*a)=1 := by rw [← Real.exp_add]; simp
  have heq : Real.exp (-t*a)*(finiteEventMass m E*Real.exp (t*a))=finiteEventMass m E := by
    calc
      _ = finiteEventMass m E*(Real.exp (-t*a)*Real.exp (t*a)) := by ring
      _ = _ := by rw [hi]; ring
  rw [heq] at hh
  exact hh

/-- One signed rectangle test, with exactly the exponent used in lem:cutconc. -/
theorem bernoulli_signed_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q c : ι → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) 1)
    (hc : ∀ i, |c i|≤2) {ε p N : ℝ} (hε : ε∈Icc (0:ℝ) 1)
    (hbudget : ∑ i, q i≤p*N/2) :
    finiteEventMass (productBernoulliMass q)
      (Finset.univ.filter (fun z => ε*p*N<bernoulliCenteredSum q c z)) ≤
      Real.exp (-ε^2*p*N/8) := by
  have ht : |ε/4|≤1/2 := by rw [abs_of_nonneg (by linarith [hε.1])]; linarith [hε.2]
  have hm := productBernoulli_exp_moment_le q c hq hc ht
  have hmark := finite_exp_markov (productBernoulliMass q) (bernoulliCenteredSum q c)
    (fun z => finiteProductMass_nonneg _ (fun i b => bernoulliMass_nonneg (hq i) b) z)
    (t:=ε/4) (a:=ε*p*N) (by linarith [hε.1])
  calc
    _ ≤ Real.exp (-(ε/4)*(ε*p*N))*Real.exp (4*(ε/4)^2*∑ i, q i) :=
      hmark.trans (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
    _ = Real.exp (4*(ε/4)^2*(∑ i, q i)-(ε/4)*(ε*p*N)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hbudget (by positivity : 0≤4*(ε/4)^2)])

/-- Union bound for any finite family of events under a nonnegative finite mass. -/
theorem finiteEventMass_union_bound {Ω K : Type*} [Fintype Ω] [Fintype K]
    [DecidableEq Ω] (m : Ω → ℝ) (hm : ∀ z, 0≤m z) (E : K → Finset Ω) :
    finiteEventMass m (Finset.univ.filter (fun z => ∃ k, z∈E k)) ≤
      ∑ k, finiteEventMass m (E k) := by
  classical
  simp only [finiteEventMass, Finset.sum_filter]
  calc
    _ ≤ ∑ z, ∑ k, if z∈E k then m z else 0 := by
      apply Finset.sum_le_sum
      intro z _
      split_ifs with hz
      · obtain ⟨k,hk⟩ := hz
        exact (show m z=(if z∈E k then m z else 0) by simp [hk]).trans_le
          (Finset.single_le_sum (f:=fun j => if z∈E j then m z else 0)
            (fun j _ => by dsimp only; split_ifs <;> simp [hm z]) (Finset.mem_univ k))
      · exact Finset.sum_nonneg (fun k _ => by split_ifs <;> simp [hm z])
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_ite_mem, Finset.univ_inter]

/-- Simultaneous absolute deviations of a finite family of coefficient vectors. -/
theorem bernoulli_test_family_tail {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (q : ι → ℝ) (c : K → ι → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) 1)
    (hc : ∀ k i, |c k i|≤2) {ε p N : ℝ} (hε : ε∈Icc (0:ℝ) 1)
    (hbudget : ∑ i, q i≤p*N/2) :
    finiteEventMass (productBernoulliMass q)
      (Finset.univ.filter (fun z => ∃ k, ε*p*N < |bernoulliCenteredSum q (c k) z|)) ≤
      2*(Fintype.card K:ℝ)*Real.exp (-ε^2*p*N/8) := by
  classical
  let cs : K×Bool → ι → ℝ := fun kb i => if kb.2 then c kb.1 i else -(c kb.1 i)
  let E : K×Bool → Finset (ι → Bool) := fun kb =>
    Finset.univ.filter (fun z => ε*p*N<bernoulliCenteredSum q (cs kb) z)
  have hneg : ∀ k z, bernoulliCenteredSum q (fun i => -(c k i)) z =
      -bernoulliCenteredSum q (c k) z := by
    intro k z; simp [bernoulliCenteredSum,neg_mul,Finset.sum_neg_distrib]
  have heq : (Finset.univ.filter (fun z => ∃ k, ε*p*N < |bernoulliCenteredSum q (c k) z|)) =
      (Finset.univ.filter (fun z => ∃ kb, z∈E kb)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k,hk⟩
      rcases lt_abs.mp hk with hh|hh
      · exact ⟨(k,true),by simpa [E,cs] using hh⟩
      · exact ⟨(k,false),by simpa [E,cs,hneg] using hh⟩
    · rintro ⟨⟨k,b⟩,hk⟩
      refine ⟨k,lt_abs.mpr ?_⟩
      cases b
      · right; simpa [E,cs,hneg] using hk
      · left; simpa [E,cs] using hk
  rw [heq]
  calc
    _ ≤ ∑ kb, finiteEventMass (productBernoulliMass q) (E kb) :=
      finiteEventMass_union_bound _ (fun z => finiteProductMass_nonneg _
        (fun i b => bernoulliMass_nonneg (hq i) b) z) E
    _ ≤ ∑ _kb : K×Bool, Real.exp (-ε^2*p*N/8) := by
      apply Finset.sum_le_sum
      intro kb _
      apply bernoulli_signed_tail q (cs kb) hq _ hε hbudget
      intro i
      cases hb : kb.2 <;> simp [cs,hb,hc]
    _ = _ := by simp [Fintype.card_prod]; ring

/-- The coefficient of an undirected edge in one rectangular matrix test. -/
def rectangleEdgeCoefficient {ι : Type*} {n : ℕ} (ends : ι → Fin n×Fin n)
    (xy : (Fin n → Bool)×(Fin n → Bool)) (i : ι) : ℝ :=
  (xy.1 (ends i).1).toNat*(xy.2 (ends i).2).toNat +
    (xy.1 (ends i).2).toNat*(xy.2 (ends i).1).toNat

theorem rectangleEdgeCoefficient_abs_le {ι : Type*} {n : ℕ} (ends : ι → Fin n×Fin n)
    (xy : (Fin n → Bool)×(Fin n → Bool)) (i : ι) :
    |rectangleEdgeCoefficient ends xy i|≤2 := by
  unfold rectangleEdgeCoefficient
  cases xy.1 (ends i).1 <;> cases xy.2 (ends i).2 <;>
    cases xy.1 (ends i).2 <;> cases xy.2 (ends i).1 <;> norm_num

/-- The finite cut-test form of lem:cutconc: union over all 4^n rectangle tests.
The edge budget applies equally to any subset of the graph's edges. -/
theorem bernoulli_rectangle_cut_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (ends : ι → Fin n×Fin n) (q : ι → ℝ)
    (hq : ∀ i, q i∈Icc (0:ℝ) 1) {ε p : ℝ} (hε : ε∈Icc (0:ℝ) 1)
    (hp : 0≤p) (hqp : ∀ i, q i≤p)
    (hcard : (Fintype.card ι:ℝ)≤(n:ℝ)^2/2) :
    finiteEventMass (productBernoulliMass q)
      (Finset.univ.filter (fun z => ∃ xy : (Fin n → Bool)×(Fin n → Bool),
        ε*p*(n:ℝ)^2 < |bernoulliCenteredSum q (rectangleEdgeCoefficient ends xy) z|)) ≤
      2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/8) := by
  have hbudget : (∑ i, q i)≤p*(n:ℝ)^2/2 := by
    calc
      _ ≤ ∑ _i : ι, p := Finset.sum_le_sum (fun i _ => hqp i)
      _ = p*(Fintype.card ι:ℝ) := by simp; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcard hp]
  have hh := bernoulli_test_family_tail q (rectangleEdgeCoefficient ends) hq
    (rectangleEdgeCoefficient_abs_le ends) hε hbudget
  have hcount : (Fintype.card ((Fin n → Bool)×(Fin n → Bool)):ℝ) = 4^n := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← mul_pow]
    norm_num
  rw [hcount] at hh
  exact hh

/-- An injectively enumerated collection of undirected, loop-free edges has at most n²/2 edges. -/
theorem edge_card_le_half_square {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (hinj : Function.Injective ends)
    (horder : ∀ i, (ends i).1<(ends i).2) :
    (Fintype.card ι:ℝ)≤(n:ℝ)^2/2 := by
  let f : ι×Bool → Fin n×Fin n := fun ib => if ib.2 then ends ib.1 else (ends ib.1).swap
  have hf : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,d⟩ h
    cases b <;> cases d
    · have hij : ends i=ends j := by simpa [f,Prod.swap_inj] using h
      exact Prod.ext (hinj hij) rfl
    · have hs : (ends i).swap=ends j := by simpa [f] using h
      have h1 := congrArg Prod.fst hs
      have h2 := congrArg Prod.snd hs
      have := horder i
      have := horder j
      simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
      rw [h1,h2] at *
      omega
    · have hs : ends i=(ends j).swap := by simpa [f] using h
      have h1 := congrArg Prod.fst hs
      have h2 := congrArg Prod.snd hs
      have := horder i
      have := horder j
      simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
      rw [h1,h2] at *
      omega
    · exact Prod.ext (hinj (by simpa [f] using h)) rfl
  have hnat := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hnat
  have hreal : (Fintype.card ι:ℝ)*2≤(n:ℝ)*(n:ℝ) := by exact_mod_cast hnat
  nlinarith

/-- Symmetric zero-diagonal matrix obtained by putting each edge weight in both positions. -/
def symmetricEdgeMatrix {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (a : ι → ℝ) (u v : Fin n) : ℝ :=
  ∑ i, ((if (u,v)=ends i then a i else 0)+(if (v,u)=ends i then a i else 0))

theorem symmetricEdgeMatrix_symm {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (a : ι → ℝ) (u v : Fin n) :
    symmetricEdgeMatrix ends a u v=symmetricEdgeMatrix ends a v u := by
  unfold symmetricEdgeMatrix
  apply Finset.sum_congr rfl
  intro i _; ring

theorem symmetricEdgeMatrix_diagonal {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (horder : ∀ i, (ends i).1<(ends i).2)
    (a : ι → ℝ) (u : Fin n) : symmetricEdgeMatrix ends a u u=0 := by
  unfold symmetricEdgeMatrix
  apply Finset.sum_eq_zero
  intro i _
  have hi : (u,u)≠ends i := by
    intro h
    have := horder i
    rw [← h] at this
    exact lt_irrefl u this
  simp [hi]

def matrixRectangleSum {n : ℕ} (Z : Fin n → Fin n → ℝ)
    (xy : (Fin n → Bool)×(Fin n → Bool)) : ℝ :=
  ∑ u, ∑ v, (xy.1 u).toNat*(xy.2 v).toNat*Z u v

/-- Matrix rectangle tests equal the edge sums with coefficients 0, 1, or 2. -/
theorem symmetricEdgeMatrix_rectangle {ι : Type*} [Fintype ι] {n : ℕ}
    (ends : ι → Fin n×Fin n) (a : ι → ℝ)
    (xy : (Fin n → Bool)×(Fin n → Bool)) :
    matrixRectangleSum (symmetricEdgeMatrix ends a) xy =
      ∑ i, rectangleEdgeCoefficient ends xy i*a i := by
  classical
  unfold matrixRectangleSum symmetricEdgeMatrix
  simp_rw [Finset.mul_sum]
  conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_add,Finset.sum_add_distrib]
  have hpair : ∀ u v : Fin n, ((u,v)=ends i) ↔ u=(ends i).1 ∧ v=(ends i).2 := by
    intro u v; exact Prod.mk_inj
  simp only [hpair, mul_ite, mul_zero]
  simp [ite_and, rectangleEdgeCoefficient]
  ring

/-- Normalized finite matrix cut norm, defined by its finitely many rectangle tests. -/
def finiteMatrixCutNorm {n : ℕ} (Z : Fin n → Fin n → ℝ) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty
    (fun xy : (Fin n → Bool)×(Fin n → Bool) => |matrixRectangleSum Z xy|))/(n:ℝ)^2

theorem finiteMatrixCutNorm_gt_iff {n : ℕ} (hn : 0<n)
    (Z : Fin n → Fin n → ℝ) (a : ℝ) :
    a<finiteMatrixCutNorm Z ↔ ∃ xy, a*(n:ℝ)^2 < |matrixRectangleSum Z xy| := by
  have hn2 : (0:ℝ)<(n:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hn)
  simp only [finiteMatrixCutNorm, lt_div_iff₀ hn2, Finset.lt_sup'_iff,
    Finset.mem_univ, true_and]

/-- Full finite matrix concentration bound for any subset of the simple graph's edges. -/
theorem bernoulli_matrix_cut_concentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0<n) (ends : ι → Fin n×Fin n)
    (hinj : Function.Injective ends) (horder : ∀ i, (ends i).1<(ends i).2)
    (q : ι → ℝ) (hq : ∀ i, q i∈Icc (0:ℝ) 1) {ε p : ℝ}
    (hε : ε∈Icc (0:ℝ) 1) (hp : 0≤p) (hqp : ∀ i, q i≤p) :
    finiteEventMass (productBernoulliMass q)
      (Finset.univ.filter (fun z => ε*p<finiteMatrixCutNorm
        (symmetricEdgeMatrix ends (fun i => (z i).toNat-q i)))) ≤
      2*4^n*Real.exp (-ε^2*p*(n:ℝ)^2/8) := by
  have heq : (Finset.univ.filter (fun z : ι → Bool => ε*p<finiteMatrixCutNorm
        (symmetricEdgeMatrix ends (fun i => (z i).toNat-q i)))) =
      (Finset.univ.filter (fun z => ∃ xy : (Fin n → Bool)×(Fin n → Bool),
        ε*p*(n:ℝ)^2 < |bernoulliCenteredSum q (rectangleEdgeCoefficient ends xy) z|)) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,
      finiteMatrixCutNorm_gt_iff hn,symmetricEdgeMatrix_rectangle,bernoulliCenteredSum]
  rw [heq]
  exact bernoulli_rectangle_cut_tail ends q hq hε hp hqp (edge_card_le_half_square ends hinj horder)

end SparseLowerTail.Section03
