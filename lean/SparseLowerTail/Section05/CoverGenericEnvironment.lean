import SparseLowerTail.Section05.ApexExpr

/-! One shared expression and derivative tree for every cover vertex.
The environment carries exact real coefficients, including fan tangency solutions.
The name apexCertificateExpr is historical: its polynomial is universal. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable def coverEnvironment (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) : Fin 24 → ℝ :=
  ![q.1.1,q.1.2,q.2,Real.exp (-q.1.1),Real.exp (-q.1.2),Real.exp (-q.2),
    criticalTriangle,criticalOmega,relaxationMultiplier π,π.1,π.2,
    θ 0,θ 1,θ 2,θ 3,θ 4,θ 5,θ 6,θ 7,θ 8,θ 9,θ 10,θ 11,lam]

@[simp] theorem apexLog_cover_realEval (i : Fin 3) (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexLog i).realEval (coverEnvironment θ lam π q) = -(![q.1.1,q.1.2,q.2] i) := by
  fin_cases i <;> rfl

@[simp] theorem apexEdge_cover_realEval (i : Fin 3) (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexEdge i).realEval (coverEnvironment θ lam π q) = Real.exp (-(![q.1.1,q.1.2,q.2] i)) := by
  fin_cases i <;> rfl

theorem apexFeature0_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 0).realEval (coverEnvironment θ lam π q) =
      certificateFeature 0 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature1_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 1).realEval (coverEnvironment θ lam π q) =
      certificateFeature 1 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature2_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 2).realEval (coverEnvironment θ lam π q) =
      certificateFeature 2 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature3_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 3).realEval (coverEnvironment θ lam π q) =
      certificateFeature 3 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature4_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 4).realEval (coverEnvironment θ lam π q) =
      certificateFeature 4 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature5_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 5).realEval (coverEnvironment θ lam π q) =
      certificateFeature 5 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature6_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 6).realEval (coverEnvironment θ lam π q) =
      certificateFeature 6 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature7_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 7).realEval (coverEnvironment θ lam π q) =
      certificateFeature 7 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature8_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 8).realEval (coverEnvironment θ lam π q) =
      certificateFeature 8 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature9_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 9).realEval (coverEnvironment θ lam π q) =
      certificateFeature 9 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature10_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 10).realEval (coverEnvironment θ lam π q) =
      certificateFeature 10 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

theorem apexFeature11_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature 11).realEval (coverEnvironment θ lam π q) =
      certificateFeature 11 (logBoxEdges q) π := by
    simp only [apexFeature,certificateFeature,Matrix.cons_val] <;>
    simp only [apexEdgeResidual,apexVertexResidual,apexEdgeTest,apexVertexTest,
      apexEntropy,apexVertexEntropy,apexVertexMean,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
      realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
      realEval_rational,realEval_var,Matrix.cons_val] <;>
    simp only [coverEnvironment,certificateFeature,cyclicAverage,coverCycle,logBoxEdges,
      coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,entropy,vertexEntropy,
      relaxationVertexMean,Matrix.cons_val,Real.log_exp] <;>
    norm_num <;> ring

@[simp] theorem apexFeature_cover_realEval (i : Fin 12) (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    (apexFeature i).realEval (coverEnvironment θ lam π q) =
      certificateFeature i (logBoxEdges q) π := by
  fin_cases i
  · exact apexFeature0_cover_realEval θ lam π q
  · exact apexFeature1_cover_realEval θ lam π q
  · exact apexFeature2_cover_realEval θ lam π q
  · exact apexFeature3_cover_realEval θ lam π q
  · exact apexFeature4_cover_realEval θ lam π q
  · exact apexFeature5_cover_realEval θ lam π q
  · exact apexFeature6_cover_realEval θ lam π q
  · exact apexFeature7_cover_realEval θ lam π q
  · exact apexFeature8_cover_realEval θ lam π q
  · exact apexFeature9_cover_realEval θ lam π q
  · exact apexFeature10_cover_realEval θ lam π q
  · exact apexFeature11_cover_realEval θ lam π q

@[simp] theorem apexHoeffding_cover_realEval (θ : Fin 12 → ℝ) (lam : ℝ) (π : ℝ×ℝ) (q : EdgeTriple) :
    apexHoeffding.realEval (coverEnvironment θ lam π q) =
      certificateHoeffding (logBoxEdges q) π := by
  simp only [apexHoeffding,apexObservable,apexEntropy,apexAverage_realEval,apexLog_cover_realEval,apexEdge_cover_realEval,
    realEval_add,realEval_sub,realEval_neg,realEval_mul,realEval_pow,realEval_zero,realEval_one,realEval_two,
    realEval_rational,realEval_var,Matrix.cons_val]
  simp only [coverEnvironment,certificateHoeffding,cyclicAverage,coverCycle,logBoxEdges,
    criticalObservable,entropy,Matrix.cons_val,Real.log_exp]

/-- Universal semantic identity, with no positivity or tangency hypotheses. -/
theorem coverCertificateExpr_realEval (θ : Fin 12 → ℝ) (lam : ℝ)
    (π : ℝ×ℝ) (q : EdgeTriple) :
    apexCertificateExpr.realEval (coverEnvironment θ lam π q) =
      logCertificate θ lam π q := by
  rw [logCertificate,apexCoverCertificateExpansion]
  simp only [apexCertificateExpr,realEval_sub,realEval_neg,realEval_add,realEval_mul,
    apexFeature_cover_realEval,apexHoeffding_cover_realEval,realEval_zero,realEval_one,
    realEval_two,realEval_rational,realEval_var]
  simp only [coverEnvironment,Matrix.cons_val]

/-- The original apex environment is the specialization at the critical point. -/
theorem coverEnvironment_apex (θ : Fin 12 → ℝ) (lam : ℝ) (q : EdgeTriple) :
    coverEnvironment θ lam criticalPoint q=apexEnvironment θ lam q := rfl
end SparseLowerTail.Section05
