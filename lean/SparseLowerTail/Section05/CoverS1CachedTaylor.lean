import SparseLowerTail.Section05.CoverS1DyadicTaylor
import SparseLowerTail.Section05.CoverS1DerivativeData

/-! Shared derivative expressions avoid recomputing symbolic differentiation
inside each numerical leaf. All replacement identities are kernel checked. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr

def s1GradientExpressions : Fin 3 → S1Expr :=
  ![s1GradientData0,s1GradientData1,s1GradientData2]
def s1HessianExpressions : Fin 3 → Fin 3 → S1Expr :=
  ![![s1HessianData00,s1HessianData01,s1HessianData02],
    ![s1HessianData10,s1HessianData11,s1HessianData12],
    ![s1HessianData20,s1HessianData21,s1HessianData22]]

theorem s1GradientExpressions_eq (i : Fin 3) : s1Partial i = s1GradientExpressions i := by
  fin_cases i
  · exact s1GradientData0_eq
  · exact s1GradientData1_eq
  · exact s1GradientData2_eq

theorem s1HessianExpressions_eq (i j : Fin 3) : s1Partial2 i j = s1HessianExpressions i j := by
  fin_cases i <;> fin_cases j
  · exact s1HessianData00_eq
  · exact s1HessianData01_eq
  · exact s1HessianData02_eq
  · exact s1HessianData10_eq
  · exact s1HessianData11_eq
  · exact s1HessianData12_eq
  · exact s1HessianData20_eq
  · exact s1HessianData21_eq
  · exact s1HessianData22_eq

def s1CachedGradientInterval (start : Fin 9 → RationalInterval)
    (velocity : Fin 3 → RationalInterval) : RationalInterval :=
  RationalInterval.sumThree (fun i => (velocity i).mul ((s1GradientExpressions i).intervalEval start))

def s1CachedHessianInterval (whole : Fin 9 → RationalInterval)
    (velocity : Fin 3 → RationalInterval) : RationalInterval :=
  RationalInterval.sumThree (fun i => RationalInterval.sumThree (fun j =>
    ((velocity i).mul (velocity j)).mul ((s1HessianExpressions i j).intervalEval whole)))

theorem s1GradientInterval_eq_cached (start : Fin 9 → RationalInterval)
    (velocity : Fin 3 → RationalInterval) :
    gradientInterval s1CertificateExpr s1PartialDirections start velocity =
      s1CachedGradientInterval start velocity := by
  unfold gradientInterval s1CachedGradientInterval
  congr 1
  funext i
  change (velocity i).mul ((s1Partial i).intervalEval start) = _
  rw [s1GradientExpressions_eq]

theorem s1HessianInterval_eq_cached (whole : Fin 9 → RationalInterval)
    (velocity : Fin 3 → RationalInterval) :
    hessianInterval s1CertificateExpr s1PartialDirections whole velocity =
      s1CachedHessianInterval whole velocity := by
  unfold hessianInterval s1CachedHessianInterval
  congr 1
  funext i
  congr 1
  funext j
  change ((velocity i).mul (velocity j)).mul ((s1Partial2 i j).intervalEval whole) = _
  rw [s1HessianExpressions_eq]

def S1TaylorBoxData.cachedMargin (D : S1TaylorBoxData) : ℚ :=
  (s1CertificateExpr.intervalEval D.start).lower+
  (s1CachedGradientInterval D.start D.velocity).lower+
  (s1CachedHessianInterval D.whole D.velocity).lower/2

theorem S1TaylorBoxData.margin_eq_cached (D : S1TaylorBoxData) : D.margin = D.cachedMargin := by
  unfold margin cachedMargin
  rw [s1GradientInterval_eq_cached,s1HessianInterval_eq_cached]

def s1CachedDyadicGradientInterval (start : Fin 9 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => (velocity i).mul ((s1GradientExpressions i).dyadicEval start))

def s1CachedDyadicHessianInterval (whole : Fin 9 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) : DyadicInterval :=
  DyadicInterval.sumThree (fun i => DyadicInterval.sumThree (fun j =>
    ((velocity i).mul (velocity j)).mul ((s1HessianExpressions i j).dyadicEval whole)))

theorem s1DyadicGradientInterval_eq_cached (start : Fin 9 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) :
    dyadicGradientInterval s1CertificateExpr s1PartialDirections start velocity =
      s1CachedDyadicGradientInterval start velocity := by
  unfold dyadicGradientInterval s1CachedDyadicGradientInterval
  congr 1
  funext i
  change (velocity i).mul ((s1Partial i).dyadicEval start) = _
  rw [s1GradientExpressions_eq]

theorem s1DyadicHessianInterval_eq_cached (whole : Fin 9 → DyadicInterval)
    (velocity : Fin 3 → DyadicInterval) :
    dyadicHessianInterval s1CertificateExpr s1PartialDirections whole velocity =
      s1CachedDyadicHessianInterval whole velocity := by
  unfold dyadicHessianInterval s1CachedDyadicHessianInterval
  congr 1
  funext i
  congr 1
  funext j
  change ((velocity i).mul (velocity j)).mul ((s1Partial2 i j).dyadicEval whole) = _
  rw [s1HessianExpressions_eq]

def S1TaylorBoxData.cachedDyadicMargin (D : S1TaylorBoxData) : ℤ :=
  2*(s1CertificateExpr.dyadicEval D.dyadicStart).lower+
  2*(s1CachedDyadicGradientInterval D.dyadicStart D.dyadicVelocity).lower+
  (s1CachedDyadicHessianInterval D.dyadicWhole D.dyadicVelocity).lower

theorem S1TaylorBoxData.dyadicMargin_eq_cached (D : S1TaylorBoxData) :
    D.dyadicMargin = D.cachedDyadicMargin := by
  unfold dyadicMargin dyadicTaylorMargin cachedDyadicMargin
  rw [s1DyadicGradientInterval_eq_cached,s1DyadicHessianInterval_eq_cached]

end SparseLowerTail.Section05
