import SparseLowerTail.Section05.CoverS1ConstantCache

/-! Integer Taylor margins using once-checked literal constant enclosures. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr

def s1CachedHornerGradient : Fin 3 → CachedPolynomialExpr 9 :=
  ![s1CachedGradient0,s1CachedGradient1,s1CachedGradient2]
def s1CachedHornerHessian : Fin 3 → Fin 3 → CachedPolynomialExpr 9 :=
  ![![s1CachedHessian00,s1CachedHessian01,s1CachedHessian02],
    ![s1CachedHessian10,s1CachedHessian11,s1CachedHessian12],
    ![s1CachedHessian20,s1CachedHessian21,s1CachedHessian22]]

theorem s1CachedValue_eval (box : Fin 9 → DyadicInterval) :
    s1CachedValue.eval box = s1CertificateExpr.dyadicEval box := by
  rw [s1CachedValue.eval_eq s1CachedValue_valid,s1CachedValue_erase]

theorem s1CachedHornerGradient_eval (i : Fin 3) (box : Fin 9 → DyadicInterval) :
    (s1CachedHornerGradient i).eval box = (s1HornerGradient i).dyadicEval box := by
  fin_cases i
  · exact (s1CachedGradient0.eval_eq s1CachedGradient0_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedGradient0_erase)
  · exact (s1CachedGradient1.eval_eq s1CachedGradient1_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedGradient1_erase)
  · exact (s1CachedGradient2.eval_eq s1CachedGradient2_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedGradient2_erase)

theorem s1CachedHornerHessian_eval (i j : Fin 3) (box : Fin 9 → DyadicInterval) :
    (s1CachedHornerHessian i j).eval box = (s1HornerHessian i j).dyadicEval box := by
  fin_cases i <;> fin_cases j
  · exact (s1CachedHessian00.eval_eq s1CachedHessian00_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian00_erase)
  · exact (s1CachedHessian01.eval_eq s1CachedHessian01_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian01_erase)
  · exact (s1CachedHessian02.eval_eq s1CachedHessian02_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian02_erase)
  · exact (s1CachedHessian10.eval_eq s1CachedHessian10_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian10_erase)
  · exact (s1CachedHessian11.eval_eq s1CachedHessian11_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian11_erase)
  · exact (s1CachedHessian12.eval_eq s1CachedHessian12_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian12_erase)
  · exact (s1CachedHessian20.eval_eq s1CachedHessian20_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian20_erase)
  · exact (s1CachedHessian21.eval_eq s1CachedHessian21_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian21_erase)
  · exact (s1CachedHessian22.eval_eq s1CachedHessian22_valid box).trans
      (congrArg (fun e : S1Expr => e.dyadicEval box) s1CachedHessian22_erase)

def s1LiteralMargin (start whole : Fin 9 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : ℤ :=
  2*(s1CachedValue.eval start).lower+
  2*(DyadicInterval.sumThree (fun i => (velocity i).mul
    ((s1CachedHornerGradient i).eval start))).lower+
  (DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    (dyadicVelocityProduct velocity i j).mul
      ((s1CachedHornerHessian i j).eval whole)))).lower

def S1TaylorBoxData.constantMargin (D : S1TaylorBoxData) : ℤ :=
  2*(s1CachedValue.eval D.dyadicStart).lower+
  2*(DyadicInterval.sumThree (fun i => (D.dyadicVelocity i).mul
    ((s1CachedHornerGradient i).eval D.dyadicStart))).lower+
  (DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    (dyadicVelocityProduct D.dyadicVelocity i j).mul
      ((s1CachedHornerHessian i j).eval D.dyadicWhole)))).lower

theorem S1TaylorBoxData.constantMargin_eq_horner (D : S1TaylorBoxData) :
    D.constantMargin=D.hornerMargin := by
  simp only [constantMargin,s1CachedValue_eval,s1CachedHornerGradient_eval,
    s1CachedHornerHessian_eval]
  rfl

theorem S1TaylorBoxData.constant_positive (D : S1TaylorBoxData)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i)
    (hm : 0 < D.constantMargin) {q : EdgeTriple} (hq : q ∈ D.box.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply D.horner_positive hl hu hc hql hqu hqc _ hq
  rwa [←D.constantMargin_eq_horner]

theorem S1TaylorBoxData.literal_positive (D : S1TaylorBoxData)
    (start whole : Fin 9 → DyadicInterval) (velocity : Fin 3 → DyadicInterval)
    (hs : ∀ i,start i=D.dyadicStart i) (hw : ∀ i,whole i=D.dyadicWhole i)
    (hv : ∀ i,velocity i=D.dyadicVelocity i)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i)
    (hm : 0 < s1LiteralMargin start whole velocity) {q : EdgeTriple}
    (hq : q ∈ D.box.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply D.constant_positive hl hu hc hql hqu hqc _ hq
  rw [funext hs,funext hw,funext hv] at hm
  exact hm

end SparseLowerTail.Section05
