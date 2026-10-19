import SparseLowerTail.Numerics.IntervalExpr
import SparseLowerTail.Section05.CoverS1FirstBox

/-! A reified exact polynomial for the S1 vertex-zero logarithmic certificate.
Variables 0–2 are q; 3–5 are exp(-q); 6,7,8 are t*, Ω*, and μ.
This is a symbolic identity. Numeric positivity requires a separate checked box. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

abbrev S1Expr := PolynomialExpr 9
def s1Log (i : Fin 3) : S1Expr := -(.var (i.castAdd 6))
def s1Edge (i : Fin 3) : S1Expr := .var ⟨i.val+3,by omega⟩
def s1Entropy (i : Fin 3) : S1Expr := s1Edge i*s1Log i-s1Edge i+1
def s1VertexEntropy (i : Fin 3) : S1Expr := s1Edge i*s1Log i-2*s1Edge i+2
def s1Observable (i : Fin 3) : S1Expr := s1Edge i+.var 7*s1Entropy i
def s1Average (a b c : S1Expr) : S1Expr := (a+b+c)*.rational (1/3)

def s1M : ℚ := (7872292148643627/36028797018963968 : ℚ)
def s1F : ℚ := (8304637712871195/18014398509481984 : ℚ)
def s1Lambda : ℚ := (1080863910568919/1125899906842624 : ℚ)
def s1Theta : Fin 12 → ℚ := ![(8639019645839429/9007199254740992 : ℚ),(-2657272677596523/562949953421312 : ℚ),(140737488299033/140737488355328 : ℚ),(-7541973450629039/36893488147419103232 : ℚ),(-8604084221028639/72057594037927936 : ℚ),(1019507261509151/1125899906842624 : ℚ),(-7199522257880297/9007199254740992 : ℚ),(8774057038934945/72057594037927936 : ℚ),(-2521529215217977/18014398509481984 : ℚ),(7097966112403971/18014398509481984 : ℚ),(-6881924343606227/9007199254740992 : ℚ),(3354424007516313/4503599627370496 : ℚ)]
def s1VertexMean : S1Expr := 1+.rational s1F-.rational s1M
def s1EdgeTest (j : Fin 5) (i : Fin 3) : S1Expr :=
  ![1,s1Edge i,s1Edge i^2,s1Edge i^3,s1Edge i*s1Log i] j
def s1VertexTest (j : Fin 4) (i : Fin 3) : S1Expr :=
  ![s1Edge i,s1Edge i^3,s1Edge i^4,s1Edge i*s1Log i] j
def s1EdgeResidual (j : Fin 5) : S1Expr :=
  s1Average (s1EdgeTest j 0*(s1Log 0+.var 8*s1Edge 1*s1Edge 2)) (s1EdgeTest j 1*(s1Log 1+.var 8*s1Edge 2*s1Edge 0)) (s1EdgeTest j 2*(s1Log 2+.var 8*s1Edge 0*s1Edge 1))
def s1VertexResidual (j : Fin 4) : S1Expr :=
  s1Average (s1VertexTest j 0*(s1VertexEntropy 1+s1VertexEntropy 2-2*s1VertexMean)) (s1VertexTest j 1*(s1VertexEntropy 2+s1VertexEntropy 0-2*s1VertexMean)) (s1VertexTest j 2*(s1VertexEntropy 0+s1VertexEntropy 1-2*s1VertexMean))
def s1Feature (i : Fin 12) : S1Expr :=
  ![s1Average (s1Edge 0) (s1Edge 1) (s1Edge 2)-.rational s1M,
    s1Edge 0*s1Edge 1*s1Edge 2-.var 6,
    s1Average (s1Entropy 0) (s1Entropy 1) (s1Entropy 2)-.rational s1F,
    s1EdgeResidual 0,
    s1EdgeResidual 1,
    s1EdgeResidual 2,
    s1EdgeResidual 3,
    s1EdgeResidual 4,
    s1VertexResidual 0,
    s1VertexResidual 1,
    s1VertexResidual 2,
    s1VertexResidual 3] i
def s1Hoeffding : S1Expr :=
  s1Average (s1Observable 0^2) (s1Observable 1^2) (s1Observable 2^2)-
  2*s1Average (s1Observable 0*s1Observable 1) (s1Observable 1*s1Observable 2)
    (s1Observable 2*s1Observable 0)+(.rational s1M+.var 7*.rational s1F)^2

def s1CertificateExpr : S1Expr :=
  -(.rational (s1Theta 0)*s1Feature 0+(.rational (s1Theta 1)*s1Feature 1+(.rational (s1Theta 2)*s1Feature 2+(.rational (s1Theta 3)*s1Feature 3+(.rational (s1Theta 4)*s1Feature 4+(.rational (s1Theta 5)*s1Feature 5+(.rational (s1Theta 6)*s1Feature 6+(.rational (s1Theta 7)*s1Feature 7+(.rational (s1Theta 8)*s1Feature 8+(.rational (s1Theta 9)*s1Feature 9+(.rational (s1Theta 10)*s1Feature 10+(.rational (s1Theta 11)*s1Feature 11+(0)))))))))))))-.rational s1Lambda*s1Hoeffding

noncomputable def s1Environment (q : EdgeTriple) : Fin 9 → ℝ :=
  ![q.1.1,q.1.2,q.2,Real.exp (-q.1.1),Real.exp (-q.1.2),Real.exp (-q.2),
    criticalTriangle,criticalOmega,relaxationMultiplier coverS1Vertex0]

@[simp] theorem s1Log_realEval (i : Fin 3) (q : EdgeTriple) :
    (s1Log i).realEval (s1Environment q) = -(![q.1.1,q.1.2,q.2] i) := by
  fin_cases i <;> rfl

@[simp] theorem s1Edge_realEval (i : Fin 3) (q : EdgeTriple) :
    (s1Edge i).realEval (s1Environment q) = Real.exp (-(![q.1.1,q.1.2,q.2] i)) := by
  fin_cases i <;> rfl

@[simp] theorem s1Average_realEval (a b c : S1Expr) (x : Fin 9 → ℝ) :
    (s1Average a b c).realEval x = (a.realEval x+b.realEval x+c.realEval x)/3 := by
  simp only [s1Average,realEval_mul,realEval_add,realEval_rational]
  norm_num
  ring

theorem s1Feature0_realEval (q : EdgeTriple) :
    (s1Feature 0).realEval (s1Environment q) =
      certificateFeature 0 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature1_realEval (q : EdgeTriple) :
    (s1Feature 1).realEval (s1Environment q) =
      certificateFeature 1 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature2_realEval (q : EdgeTriple) :
    (s1Feature 2).realEval (s1Environment q) =
      certificateFeature 2 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature3_realEval (q : EdgeTriple) :
    (s1Feature 3).realEval (s1Environment q) =
      certificateFeature 3 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature4_realEval (q : EdgeTriple) :
    (s1Feature 4).realEval (s1Environment q) =
      certificateFeature 4 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature5_realEval (q : EdgeTriple) :
    (s1Feature 5).realEval (s1Environment q) =
      certificateFeature 5 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature6_realEval (q : EdgeTriple) :
    (s1Feature 6).realEval (s1Environment q) =
      certificateFeature 6 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature7_realEval (q : EdgeTriple) :
    (s1Feature 7).realEval (s1Environment q) =
      certificateFeature 7 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature8_realEval (q : EdgeTriple) :
    (s1Feature 8).realEval (s1Environment q) =
      certificateFeature 8 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature9_realEval (q : EdgeTriple) :
    (s1Feature 9).realEval (s1Environment q) =
      certificateFeature 9 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature10_realEval (q : EdgeTriple) :
    (s1Feature 10).realEval (s1Environment q) =
      certificateFeature 10 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem s1Feature11_realEval (q : EdgeTriple) :
    (s1Feature 11).realEval (s1Environment q) =
      certificateFeature 11 (logBoxEdges q) coverS1Vertex0 := by
    simp only [s1Feature,certificateFeature,Matrix.cons_val] <;>
    simp only [s1EdgeResidual,s1VertexResidual,s1EdgeTest,s1VertexTest,
      s1Entropy,s1VertexEntropy,s1VertexMean,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [s1Environment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

@[simp] theorem s1Feature_realEval (i : Fin 12) (q : EdgeTriple) :
    (s1Feature i).realEval (s1Environment q) =
      certificateFeature i (logBoxEdges q) coverS1Vertex0 := by
  fin_cases i
  · exact s1Feature0_realEval q
  · exact s1Feature1_realEval q
  · exact s1Feature2_realEval q
  · exact s1Feature3_realEval q
  · exact s1Feature4_realEval q
  · exact s1Feature5_realEval q
  · exact s1Feature6_realEval q
  · exact s1Feature7_realEval q
  · exact s1Feature8_realEval q
  · exact s1Feature9_realEval q
  · exact s1Feature10_realEval q
  · exact s1Feature11_realEval q

@[simp] theorem s1Hoeffding_realEval (q : EdgeTriple) :
    s1Hoeffding.realEval (s1Environment q) =
      certificateHoeffding (logBoxEdges q) coverS1Vertex0 := by
  simp only [s1Hoeffding,s1Observable,s1Entropy,s1Average_realEval,s1Log_realEval,s1Edge_realEval,
    realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
    realEval_rational,realEval_var,Matrix.cons_val]
  simp only [s1Environment,certificateHoeffding,cyclicAverage,coverCycle,logBoxEdges,
    criticalObservable,entropy,coverS1Vertex0,s1M,s1F,Matrix.cons_val,Real.log_exp]
  norm_num

/-- Exact symbolic identity with the certificate from the paper and data file. -/
theorem s1CertificateExpr_realEval (q : EdgeTriple) :
    s1CertificateExpr.realEval (s1Environment q) =
      logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  rw [logCertificate,coverCertificate_fin12_expansion]
  simp only [s1CertificateExpr,realEval_sub,realEval_neg,realEval_add,realEval_mul,
    s1Feature_realEval,s1Hoeffding_realEval,realEval_zero,realEval_one,realEval_two,realEval_rational,realEval_var]
  simp only [s1Theta,s1Lambda,coverS1Theta,coverS1Lam,Matrix.cons_val]
  norm_num

end SparseLowerTail.Section05
