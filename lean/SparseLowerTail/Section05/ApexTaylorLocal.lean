import SparseLowerTail.Section05.ApexLocalIntervals
import SparseLowerTail.Numerics.TaylorThird

/-! Actual third derivatives and the paper's third-order local certificate.
The neighborhood radius is an input; it is not reduced by this argument. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics Certificate Set

abbrev ApexThirdBounds := Fin 3 → Fin 3 → Fin 3 → ℝ

def apexThird (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i j k : Fin 3) : ℝ :=
  (((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).along
    (apexPartials k)).realEval (apexVariables θ lam q)

def apexThirdForm (θ : Fin 12 → ℝ) (lam : ℝ) (q v : ApexVector) : ℝ :=
  ∑i,∑j,∑k,v i*v j*v k*apexThird θ lam q i j k

theorem apexHessian_segment_deriv (θ : Fin 12 → ℝ) (lam : ℝ)
    (p v : ApexVector) (s : ℝ) (i j : Fin 3) :
    HasDerivAt (fun t => apexHessian θ lam (familySegment p v t) i j)
      (sumThree (fun k => v k*apexThird θ lam (familySegment p v s) i j k)) s := by
  simpa only [apexHessian,apexThird,sumThree,PolynomialExpr.derivative,
    PolynomialExpr.realEval_simplify] using
    ((apexCertificateExpr.along (apexPartials i)).along (apexPartials j)).hasDerivAt_three
       apexPartials v (apexVariables_segment_deriv θ lam p v s)

theorem apexHessianForm_third_deriv (θ : Fin 12 → ℝ) (lam : ℝ)
    (p v : ApexVector) (s : ℝ) :
    HasDerivAt (fun t => apexHessianForm θ lam (familySegment p v t) v)
      (apexThirdForm θ lam (familySegment p v s) v) s := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (apexHessian_segment_deriv θ lam p v s i j).const_mul (v i*v j)))
  convert h using 1
  · funext t
    simp only [apexHessianForm,sumThree,Fin.sum_univ_three,Pi.add_apply] <;> ring
  · simp only [apexThirdForm,sumThree,Fin.sum_univ_three]
    ring

theorem apexNormSq_nonneg (v : ApexVector) : 0≤apexNormSq v := by
  unfold apexNormSq sumThree
  positivity

theorem apex_sq_le_normSq (v : ApexVector) (i : Fin 3) : (v i)^2≤apexNormSq v := by
  fin_cases i
  · change (v 0)^2 ≤ (v 0)^2+(v 1)^2+(v 2)^2
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]
  · change (v 1)^2 ≤ (v 0)^2+(v 1)^2+(v 2)^2
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]
  · change (v 2)^2 ≤ (v 0)^2+(v 1)^2+(v 2)^2
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]

theorem apexNormSq_pos {v : ApexVector} (hv : v≠0) : 0<apexNormSq v := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  exact (sq_pos_of_ne_zero hi).trans_le (apex_sq_le_normSq v i)

theorem apex_abs_triple_le {v : ApexVector} {δ : ℝ} (hδ : 0≤δ)
    (hv : ∀i,|v i|≤δ) (i j k : Fin 3) : |v i*v j*v k|≤δ*apexNormSq v := by
  have hprod : |v j| * |v k|≤apexNormSq v := by
    have hj := apex_sq_le_normSq v j
    have hk := apex_sq_le_normSq v k
    nlinarith only [hj,hk,sq_nonneg (|v j| - |v k|),sq_abs (v j),sq_abs (v k)]
  calc
    |v i*v j*v k|=|v i| * (|v j| * |v k|) := by simp only [abs_mul,mul_assoc]
    _ ≤ δ*apexNormSq v := mul_le_mul (hv i) hprod (by positivity) hδ

theorem apexThirdForm_bound (θ : Fin 12 → ℝ) (lam : ℝ)
    (q v : ApexVector) (C : ApexThirdBounds) {δ : ℝ} (hδ : 0≤δ)
    (hv : ∀i,|v i|≤δ) (hC : ∀i j k,|apexThird θ lam q i j k|≤C i j k) :
    |apexThirdForm θ lam q v|≤(∑i,∑j,∑k,C i j k)*(δ*apexNormSq v) := by
  have hterm (i j k : Fin 3) :
      |v i*v j*v k*apexThird θ lam q i j k|≤C i j k*(δ*apexNormSq v) := by
    rw [abs_mul]
    simpa only [mul_comm] using mul_le_mul (apex_abs_triple_le hδ hv i j k)
      (hC i j k) (abs_nonneg _) (mul_nonneg hδ (apexNormSq_nonneg v))
  unfold apexThirdForm
  calc
    |∑i,∑j,∑k,v i*v j*v k*apexThird θ lam q i j k|
        ≤ ∑i,∑j,∑k,|v i*v j*v k*apexThird θ lam q i j k| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑i,∑j,∑k,C i j k*(δ*apexNormSq v) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => hterm i j k
    _ = (∑i,∑j,∑k,C i j k)*(δ*apexNormSq v) := by
      simp only [Finset.sum_mul]

/-- The actual local certificate follows from the paper's strict third-order
margin at its stated radius. All numerical bounds remain explicit inputs. -/
theorem apexPhi_local_of_third_bounds {θ : Fin 12 → ℝ} {lam δ ell : ℝ}
    {p q : ApexVector} (hδ : 0≤δ) (hell : 0<ell)
    (hval : apexPhi θ lam p=0) (hgrad : ∀i,apexGradient θ lam p i=0)
    (hH : ∀v,ell*apexNormSq v≤apexHessianForm θ lam p v)
    (C : ApexThirdBounds)
    (hC : ∀r∈familyCube p δ,∀i j k,|apexThird θ lam r i j k|≤C i j k)
    (hmargin : δ*(∑i,∑j,∑k,C i j k)<3*ell)
    (hq : q∈familyCube p δ) :
    0≤apexPhi θ lam q ∧ (apexPhi θ lam q=0 ↔ q=p) := by
  by_cases he : q=p
  · subst q
    simp [hval]
  let v := q-p
  have hv : v≠0 := sub_ne_zero.mpr he
  have hp : p∈familyCube p δ := by intro i; simpa using hδ
  have hcoord : ∀i,|v i|≤δ := hq
  let S : ℝ := ∑i,∑j,∑k,C i j k
  have hlow : ∀s∈Icc (0:ℝ) 1,-(S*δ*apexNormSq v)≤
      apexThirdForm θ lam (familySegment p v s) v := by
    intro s hs
    have hmem := familySegment_mem_convex (familyCube_convex p δ) hp hq hs
    have hh := apexThirdForm_bound θ lam (familySegment p v s) v C hδ hcoord (hC _ hmem)
    simpa only [S,mul_assoc] using (abs_le.mp hh).1
  have ht := segment_taylor3_lower
    (fun s _ => apexPhi_segment_deriv θ lam p v s)
    (fun s _ => apexHessianForm_segment_deriv θ lam p v s)
    (fun s _ => apexHessianForm_third_deriv θ lam p v s) hlow
  have hh := hH v
  have hN := apexNormSq_pos hv
  have hm : 0<(ell/2-δ*S/6)*apexNormSq v := by
    apply mul_pos _ hN
    dsimp [S]
    linarith only [hmargin,hell]
  have hs0 : familySegment p v 0=p := familySegment_zero p v
  have hs1 : familySegment p v 1=q := familySegment_sub_one p q
  rw [hs0,hs1,hval] at ht
  simp only [hgrad,mul_zero,sumThree,add_zero,zero_add] at ht
  have hpos : 0<apexPhi θ lam q := by nlinarith
  exact ⟨hpos.le,⟨fun hz => (ne_of_gt hpos hz).elim,fun h => (he h).elim⟩⟩

end SparseLowerTail.Section05
