import SparseLowerTail.Section05.CoverS1Program

/-! Shared-register Taylor evaluation and its exact equality to the previously
proved interval formula. All numerical replay remains inside the kernel. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr

def s1ProgramRun (box : Fin 9 → DyadicInterval) : RegisterTree DyadicInterval :=
  IntervalProgram.dyadic s1Program s1ProgramDepth box

def s1ProgramGradientOutputs : Fin 3 → ℕ :=
  ![s1ProgramGradient0,s1ProgramGradient1,s1ProgramGradient2]
def s1ProgramHessianOutputs : Fin 3 → Fin 3 → ℕ :=
  ![![s1ProgramHessian00,s1ProgramHessian01,s1ProgramHessian02],
    ![s1ProgramHessian10,s1ProgramHessian11,s1ProgramHessian12],
    ![s1ProgramHessian20,s1ProgramHessian21,s1ProgramHessian22]]

theorem s1Program_value (box : Fin 9 → DyadicInterval) :
    (s1ProgramRun box).get s1ProgramValue = s1CertificateExpr.dyadicEval box := by
  rw [s1ProgramRun,IntervalProgram.dyadic_eq,s1ProgramValue_eq]

theorem s1Program_gradient (box : Fin 9 → DyadicInterval) (i : Fin 3) :
    (s1ProgramRun box).get (s1ProgramGradientOutputs i) =
      (s1GradientExpressions i).dyadicEval box := by
  rw [s1ProgramRun,IntervalProgram.dyadic_eq]
  fin_cases i
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramGradient0_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramGradient1_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramGradient2_eq

theorem s1Program_hessian (box : Fin 9 → DyadicInterval) (i j : Fin 3) :
    (s1ProgramRun box).get (s1ProgramHessianOutputs i j) =
      (s1HessianExpressions i j).dyadicEval box := by
  rw [s1ProgramRun,IntervalProgram.dyadic_eq]
  fin_cases i <;> fin_cases j
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian00_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian01_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian02_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian10_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian11_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian12_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian20_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian21_eq
  · exact congrArg (fun e : S1Expr => e.dyadicEval box) s1ProgramHessian22_eq

def S1TaylorBoxData.programMargin (D : S1TaylorBoxData) : ℤ :=
  let st := s1ProgramRun D.dyadicStart
  let wh := s1ProgramRun D.dyadicWhole
  let g := DyadicInterval.sumThree (fun i =>
    (D.dyadicVelocity i).mul (st.get (s1ProgramGradientOutputs i)))
  let h := DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    ((D.dyadicVelocity i).mul (D.dyadicVelocity j)).mul (wh.get (s1ProgramHessianOutputs i j))))
  2*(st.get s1ProgramValue).lower+2*g.lower+h.lower

theorem S1TaylorBoxData.programMargin_eq_cached (D : S1TaylorBoxData) :
    D.programMargin = D.cachedDyadicMargin := by
  simp only [programMargin,s1Program_value,s1Program_gradient,s1Program_hessian]
  rfl

theorem S1TaylorBoxData.program_positive (D : S1TaylorBoxData)
    (hl : ∀ i, (D.lowerExp i).Valid) (hu : ∀ i, (D.upperExp i).Valid)
    (hc : ∀ i, (D.centerExp i).Valid)
    (hql : ∀ i, (D.lowerExp i).q = D.box.lower i)
    (hqu : ∀ i, (D.upperExp i).q = D.box.upper i)
    (hqc : ∀ i, (D.centerExp i).q = D.box.centerCoordinate i)
    (hm : 0 < D.programMargin) {q : EdgeTriple} (hq : q ∈ D.box.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  apply D.dyadic_positive hl hu hc hql hqu hqc _ hq
  rwa [D.dyadicMargin_eq_cached,← D.programMargin_eq_cached]

end SparseLowerTail.Section05
