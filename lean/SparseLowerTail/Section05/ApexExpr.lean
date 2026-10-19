import SparseLowerTail.Numerics.IntervalExpr
import SparseLowerTail.Section05.LogBoxSubdivision
import SparseLowerTail.Section05.FiniteCover

/-! Exact symbolic expression for the cover certificate at its critical apex.
Variables: q[0:3], exp(-q)[3:6], t*, Ω*, μ*, m*, F*, θ[0:12], λ.
All coefficients remain real parameters; subsequent interval checks must enclose
the exact tangency solution, not rounded substitutes. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev ApexExpr := PolynomialExpr 24
def apexLog (i : Fin 3) : ApexExpr := -(.var (i.castAdd 21))
def apexEdge (i : Fin 3) : ApexExpr := .var ⟨i.val+3,by omega⟩
def apexEntropy (i : Fin 3) : ApexExpr := apexEdge i*apexLog i-apexEdge i+1
def apexVertexEntropy (i : Fin 3) : ApexExpr := apexEdge i*apexLog i-2*apexEdge i+2
def apexObservable (i : Fin 3) : ApexExpr := apexEdge i+.var 7*apexEntropy i
def apexAverage (a b c : ApexExpr) : ApexExpr := (a+b+c)*.rational (1/3)

def apexVertexMean : ApexExpr := 1+.var 10-.var 9
def apexEdgeTest (j : Fin 5) (i : Fin 3) : ApexExpr :=
  ![1,apexEdge i,apexEdge i^2,apexEdge i^3,apexEdge i*apexLog i] j
def apexVertexTest (j : Fin 4) (i : Fin 3) : ApexExpr :=
  ![apexEdge i,apexEdge i^3,apexEdge i^4,apexEdge i*apexLog i] j
def apexEdgeResidual (j : Fin 5) : ApexExpr :=
  apexAverage (apexEdgeTest j 0*(apexLog 0+.var 8*apexEdge 1*apexEdge 2)) (apexEdgeTest j 1*(apexLog 1+.var 8*apexEdge 2*apexEdge 0)) (apexEdgeTest j 2*(apexLog 2+.var 8*apexEdge 0*apexEdge 1))
def apexVertexResidual (j : Fin 4) : ApexExpr :=
  apexAverage (apexVertexTest j 0*(apexVertexEntropy 1+apexVertexEntropy 2-2*apexVertexMean)) (apexVertexTest j 1*(apexVertexEntropy 2+apexVertexEntropy 0-2*apexVertexMean)) (apexVertexTest j 2*(apexVertexEntropy 0+apexVertexEntropy 1-2*apexVertexMean))
def apexFeature (i : Fin 12) : ApexExpr :=
  ![apexAverage (apexEdge 0) (apexEdge 1) (apexEdge 2)-.var 9,
    apexEdge 0*apexEdge 1*apexEdge 2-.var 6,
    apexAverage (apexEntropy 0) (apexEntropy 1) (apexEntropy 2)-.var 10,
    apexEdgeResidual 0,
    apexEdgeResidual 1,
    apexEdgeResidual 2,
    apexEdgeResidual 3,
    apexEdgeResidual 4,
    apexVertexResidual 0,
    apexVertexResidual 1,
    apexVertexResidual 2,
    apexVertexResidual 3] i
def apexHoeffding : ApexExpr :=
  apexAverage (apexObservable 0^2) (apexObservable 1^2) (apexObservable 2^2)-
  2*apexAverage (apexObservable 0*apexObservable 1) (apexObservable 1*apexObservable 2)
    (apexObservable 2*apexObservable 0)+(.var 9+.var 7*.var 10)^2

def apexCertificateExpr : ApexExpr :=
  -(.var 11*apexFeature 0+(.var 12*apexFeature 1+(.var 13*apexFeature 2+(.var 14*apexFeature 3+(.var 15*apexFeature 4+(.var 16*apexFeature 5+(.var 17*apexFeature 6+(.var 18*apexFeature 7+(.var 19*apexFeature 8+(.var 20*apexFeature 9+(.var 21*apexFeature 10+(.var 22*apexFeature 11+(0)))))))))))))-.var 23*apexHoeffding

noncomputable def apexEnvironment (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) : Fin 24 → ℝ :=
  ![q.1.1,q.1.2,q.2,Real.exp (-q.1.1),Real.exp (-q.1.2),Real.exp (-q.2),
    criticalTriangle,criticalOmega,relaxationMultiplier criticalPoint,criticalMean,criticalCost,
    θ 0,θ 1,θ 2,θ 3,θ 4,θ 5,θ 6,θ 7,θ 8,θ 9,θ 10,θ 11,lam]

@[simp] theorem apexLog_realEval (i : Fin 3) (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexLog i).realEval (apexEnvironment θ lam q) = -(![q.1.1,q.1.2,q.2] i) := by
  fin_cases i <;> rfl

@[simp] theorem apexEdge_realEval (i : Fin 3) (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexEdge i).realEval (apexEnvironment θ lam q) = Real.exp (-(![q.1.1,q.1.2,q.2] i)) := by
  fin_cases i <;> rfl

@[simp] theorem apexAverage_realEval (a b c : ApexExpr) (x : Fin 24 → ℝ) :
    (apexAverage a b c).realEval x = (a.realEval x+b.realEval x+c.realEval x)/3 := by
  simp only [apexAverage,realEval_mul,realEval_add,realEval_rational]
  norm_num
  ring

theorem apexFeature0_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 0).realEval (apexEnvironment θ lam q) =
      certificateFeature 0 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature1_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 1).realEval (apexEnvironment θ lam q) =
      certificateFeature 1 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature2_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 2).realEval (apexEnvironment θ lam q) =
      certificateFeature 2 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature3_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 3).realEval (apexEnvironment θ lam q) =
      certificateFeature 3 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature4_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 4).realEval (apexEnvironment θ lam q) =
      certificateFeature 4 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature5_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 5).realEval (apexEnvironment θ lam q) =
      certificateFeature 5 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature6_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 6).realEval (apexEnvironment θ lam q) =
      certificateFeature 6 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature7_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 7).realEval (apexEnvironment θ lam q) =
      certificateFeature 7 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature8_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 8).realEval (apexEnvironment θ lam q) =
      certificateFeature 8 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature9_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 9).realEval (apexEnvironment θ lam q) =
      certificateFeature 9 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature10_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 10).realEval (apexEnvironment θ lam q) =
      certificateFeature 10 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature11_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature 11).realEval (apexEnvironment θ lam q) =
      certificateFeature 11 (logBoxEdges q) criticalPoint := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [apexEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,criticalPoint,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

@[simp] theorem apexFeature_realEval (i : Fin 12) (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    (apexFeature i).realEval (apexEnvironment θ lam q) =
      certificateFeature i (logBoxEdges q) criticalPoint := by
  fin_cases i
  · exact apexFeature0_realEval θ lam q
  · exact apexFeature1_realEval θ lam q
  · exact apexFeature2_realEval θ lam q
  · exact apexFeature3_realEval θ lam q
  · exact apexFeature4_realEval θ lam q
  · exact apexFeature5_realEval θ lam q
  · exact apexFeature6_realEval θ lam q
  · exact apexFeature7_realEval θ lam q
  · exact apexFeature8_realEval θ lam q
  · exact apexFeature9_realEval θ lam q
  · exact apexFeature10_realEval θ lam q
  · exact apexFeature11_realEval θ lam q

@[simp] theorem apexHoeffding_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    apexHoeffding.realEval (apexEnvironment θ lam q) =
      certificateHoeffding (logBoxEdges q) criticalPoint := by
  simp only [apexHoeffding,apexObservable,apexEntropy,apexAverage_realEval,apexLog_realEval,apexEdge_realEval,
    realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
    realEval_rational,realEval_var,Matrix.cons_val]
  simp only [apexEnvironment,certificateHoeffding,cyclicAverage,coverCycle,logBoxEdges,
    criticalObservable,entropy,criticalPoint,Matrix.cons_val,Real.log_exp]

theorem apexCoverCertificateExpansion (θ : Fin 12 → ℝ) (lam : ℝ)
    (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam u π = -(θ 0*certificateFeature 0 u π+(θ 1*certificateFeature 1 u π+(θ 2*certificateFeature 2 u π+(θ 3*certificateFeature 3 u π+(θ 4*certificateFeature 4 u π+(θ 5*certificateFeature 5 u π+(θ 6*certificateFeature 6 u π+(θ 7*certificateFeature 7 u π+(θ 8*certificateFeature 8 u π+(θ 9*certificateFeature 9 u π+(θ 10*certificateFeature 10 u π+(θ 11*certificateFeature 11 u π+0))))))))))))-lam*certificateHoeffding u π := by
  unfold coverCertificate
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  rfl

/-- Exact symbolic identity with the certificate from the paper and data file. -/
theorem apexCertificateExpr_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    apexCertificateExpr.realEval (apexEnvironment θ lam q) =
      logCertificate θ lam criticalPoint q := by
  rw [logCertificate,apexCoverCertificateExpansion]
  simp only [apexCertificateExpr,realEval_sub,realEval_neg,realEval_add,realEval_mul,
    apexFeature_realEval,apexHoeffding_realEval,realEval_zero,realEval_one,realEval_two,realEval_rational,realEval_var]
  simp only [apexEnvironment,Matrix.cons_val]

end SparseLowerTail.Section05
