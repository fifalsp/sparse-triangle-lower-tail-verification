import SparseLowerTail.Section05.CoverConstantBounds
import SparseLowerTail.Section05.SortedLogBoxes

/-! First actual proof-producing non-apex cover calculation.
Stable manuscript anchor `prop:cover`, cell S1, first printed parameter vertex.
The exact original dyadic coefficients are read from data/cover.json.
This proves positivity ONLY on 0 ≤ qᵢ ≤ 1/1024. The rest of S1 and every
other cell still require checked partitions; this is not the full cover theorem.
Regenerate from lean/ with python3 tools/generate_cover_s1_box.py. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04 Numerics
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem coverCertificate_fin12_expansion (θ : Fin 12 → ℝ) (lam : ℝ)
    (u : EdgeTriple) (π : ℝ × ℝ) :
    coverCertificate θ lam u π = -(θ 0*certificateFeature 0 u π+(θ 1*certificateFeature 1 u π+(θ 2*certificateFeature 2 u π+(θ 3*certificateFeature 3 u π+(θ 4*certificateFeature 4 u π+(θ 5*certificateFeature 5 u π+(θ 6*certificateFeature 6 u π+(θ 7*certificateFeature 7 u π+(θ 8*certificateFeature 8 u π+(θ 9*certificateFeature 9 u π+(θ 10*certificateFeature 10 u π+(θ 11*certificateFeature 11 u π+0))))))))))))-lam*certificateHoeffding u π := by
  unfold coverCertificate
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  rfl

def coverS1Theta : Fin 12 → ℝ := ![(8639019645839429/9007199254740992 : ℝ),(-2657272677596523/562949953421312 : ℝ),(140737488299033/140737488355328 : ℝ),(-7541973450629039/36893488147419103232 : ℝ),(-8604084221028639/72057594037927936 : ℝ),(1019507261509151/1125899906842624 : ℝ),(-7199522257880297/9007199254740992 : ℝ),(8774057038934945/72057594037927936 : ℝ),(-2521529215217977/18014398509481984 : ℝ),(7097966112403971/18014398509481984 : ℝ),(-6881924343606227/9007199254740992 : ℝ),(3354424007516313/4503599627370496 : ℝ)]
def coverS1Lam : ℝ := (1080863910568919/1125899906842624 : ℝ)
def coverS1Q : ℝ := (6743/512 : ℝ)
def coverS1Vertex0 : ℝ × ℝ := ((7872292148643627/36028797018963968 : ℝ),(8304637712871195/18014398509481984 : ℝ))

/-- Elementary exponential enclosure, uniform on the entire first dyadic box. -/
theorem exp_neg_first_box {x : ℝ} (hx : x ∈ Set.Icc 0 (1/1024 : ℝ)) :
    Bounds (Real.exp (-x)) (1023/1024) 1 := by
  constructor
  · have h := Real.add_one_le_exp (-x)
    linarith [hx.2]
  · simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (neg_nonpos.mpr hx.1))


theorem coverS1_hmu_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (relaxationMultiplier coverS1Vertex0) (173856571583/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
  let v1 : ℝ := (1 : ℝ)-(8304637712871195/18014398509481984 : ℝ)
  have h1 : Bounds v1 (5389999999/10000000000 : ℝ) (539/1000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (8304637712871195/18014398509481984 : ℝ))).weaken (by norm_num) (by norm_num)
  let v2 : ℝ := v1-(7872292148643627/36028797018963968 : ℝ)
  have h2 : Bounds v2 (3204999999/10000000000 : ℝ) (3205000001/10000000000 : ℝ) := by
    exact (h1.sub (Bounds.refl (7872292148643627/36028797018963968 : ℝ))).weaken (by norm_num) (by norm_num)
  let v3 : ℝ := v2/criticalTriangle
  have h3 : Bounds v3 (173856571583/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (h2.div_pos criticalTriangle_checked_bounds (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have hmu : Bounds (relaxationMultiplier coverS1Vertex0) (173856571583/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    convert h3 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v1,v2,v3] <;> ring
  exact hmu

theorem coverS1_hk_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (relaxationVertexMean coverS1Vertex0) (497/400 : ℝ) (6212500001/5000000000 : ℝ) := by
  let v4 : ℝ := (1 : ℝ)+(8304637712871195/18014398509481984 : ℝ)
  have h4 : Bounds v4 (1461/1000 : ℝ) (14610000001/10000000000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).add (Bounds.refl (8304637712871195/18014398509481984 : ℝ))).weaken (by norm_num) (by norm_num)
  let v5 : ℝ := v4-(7872292148643627/36028797018963968 : ℝ)
  have h5 : Bounds v5 (497/400 : ℝ) (6212500001/5000000000 : ℝ) := by
    exact (h4.sub (Bounds.refl (7872292148643627/36028797018963968 : ℝ))).weaken (by norm_num) (by norm_num)
  have hk : Bounds (relaxationVertexMean coverS1Vertex0) (497/400 : ℝ) (6212500001/5000000000 : ℝ) := by
    convert h5 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v4,v5] <;> ring
  exact hk

theorem coverS1_he0_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (entropy (Real.exp (-qv.1.1))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := v6-(Real.exp (-qv.1.1))
  have h9 : Bounds v9 (-1025/1024 : ℝ) (-1023/1024 : ℝ) := by
    exact (h6.sub hx).weaken (by norm_num) (by norm_num)
  let v10 : ℝ := v9+(1 : ℝ)
  have h10 : Bounds v10 (-1/1024 : ℝ) (1/1024 : ℝ) := by
    exact (h9.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he0 : Bounds (entropy (Real.exp (-qv.1.1))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
    convert h10 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v9,v10] <;> ring
  exact he0

theorem coverS1_hve0_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (vertexEntropy (Real.exp (-qv.1.1))) (-1/1024 : ℝ) (1/512 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v11 : ℝ := (2 : ℝ)*(Real.exp (-qv.1.1))
  have h11 : Bounds v11 (1023/512 : ℝ) (2 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v12 : ℝ := v6-v11
  have h12 : Bounds v12 (-2049/1024 : ℝ) (-1023/512 : ℝ) := by
    exact (h6.sub h11).weaken (by norm_num) (by norm_num)
  let v13 : ℝ := v12+(2 : ℝ)
  have h13 : Bounds v13 (-1/1024 : ℝ) (1/512 : ℝ) := by
    exact (h12.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve0 : Bounds (vertexEntropy (Real.exp (-qv.1.1))) (-1/1024 : ℝ) (1/512 : ℝ) := by
    convert h13 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v11,v12,v13] <;> ring
  exact hve0

theorem coverS1_hg0_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (criticalObservable (Real.exp (-qv.1.1))) (1023/1024 : ℝ) (513/512 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have he0 := coverS1_he0_bounds hq
  have he0p : Bounds (entropy (Real.exp (-qv.1.1))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he0.2⟩
  let v14 : ℝ := criticalOmega*(entropy (Real.exp (-qv.1.1)))
  have h14 : Bounds v14 (0 : ℝ) (1/512 : ℝ) := by
    exact criticalOmega_coarse_bounds.mul_corners he0p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v15 : ℝ := (Real.exp (-qv.1.1))+v14
  have h15 : Bounds v15 (1023/1024 : ℝ) (513/512 : ℝ) := by
    exact (hx.add h14).weaken (by norm_num) (by norm_num)
  have hg0 : Bounds (criticalObservable (Real.exp (-qv.1.1))) (1023/1024 : ℝ) (513/512 : ℝ) := by
    convert h15 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v14,v15] <;> ring
  exact hg0

theorem coverS1_he1_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (entropy (Real.exp (-qv.1.2))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
  have hy := exp_neg_first_box hq.2.1
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v16 : ℝ := v7-(Real.exp (-qv.1.2))
  have h16 : Bounds v16 (-1025/1024 : ℝ) (-1023/1024 : ℝ) := by
    exact (h7.sub hy).weaken (by norm_num) (by norm_num)
  let v17 : ℝ := v16+(1 : ℝ)
  have h17 : Bounds v17 (-1/1024 : ℝ) (1/1024 : ℝ) := by
    exact (h16.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he1 : Bounds (entropy (Real.exp (-qv.1.2))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
    convert h17 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v7,v16,v17] <;> ring
  exact he1

theorem coverS1_hve1_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (vertexEntropy (Real.exp (-qv.1.2))) (-1/1024 : ℝ) (1/512 : ℝ) := by
  have hy := exp_neg_first_box hq.2.1
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v18 : ℝ := (2 : ℝ)*(Real.exp (-qv.1.2))
  have h18 : Bounds v18 (1023/512 : ℝ) (2 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v19 : ℝ := v7-v18
  have h19 : Bounds v19 (-2049/1024 : ℝ) (-1023/512 : ℝ) := by
    exact (h7.sub h18).weaken (by norm_num) (by norm_num)
  let v20 : ℝ := v19+(2 : ℝ)
  have h20 : Bounds v20 (-1/1024 : ℝ) (1/512 : ℝ) := by
    exact (h19.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve1 : Bounds (vertexEntropy (Real.exp (-qv.1.2))) (-1/1024 : ℝ) (1/512 : ℝ) := by
    convert h20 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v7,v18,v19,v20] <;> ring
  exact hve1

theorem coverS1_hg1_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (criticalObservable (Real.exp (-qv.1.2))) (1023/1024 : ℝ) (513/512 : ℝ) := by
  have hy := exp_neg_first_box hq.2.1
  have he1 := coverS1_he1_bounds hq
  have he1p : Bounds (entropy (Real.exp (-qv.1.2))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he1.2⟩
  let v21 : ℝ := criticalOmega*(entropy (Real.exp (-qv.1.2)))
  have h21 : Bounds v21 (0 : ℝ) (1/512 : ℝ) := by
    exact criticalOmega_coarse_bounds.mul_corners he1p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v22 : ℝ := (Real.exp (-qv.1.2))+v21
  have h22 : Bounds v22 (1023/1024 : ℝ) (513/512 : ℝ) := by
    exact (hy.add h21).weaken (by norm_num) (by norm_num)
  have hg1 : Bounds (criticalObservable (Real.exp (-qv.1.2))) (1023/1024 : ℝ) (513/512 : ℝ) := by
    convert h22 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v21,v22] <;> ring
  exact hg1

theorem coverS1_he2_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (entropy (Real.exp (-qv.2))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
  have hz := exp_neg_first_box hq.2.2
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v23 : ℝ := v8-(Real.exp (-qv.2))
  have h23 : Bounds v23 (-1025/1024 : ℝ) (-1023/1024 : ℝ) := by
    exact (h8.sub hz).weaken (by norm_num) (by norm_num)
  let v24 : ℝ := v23+(1 : ℝ)
  have h24 : Bounds v24 (-1/1024 : ℝ) (1/1024 : ℝ) := by
    exact (h23.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he2 : Bounds (entropy (Real.exp (-qv.2))) (-1/1024 : ℝ) (1/1024 : ℝ) := by
    convert h24 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v8,v23,v24] <;> ring
  exact he2

theorem coverS1_hve2_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (vertexEntropy (Real.exp (-qv.2))) (-1/1024 : ℝ) (1/512 : ℝ) := by
  have hz := exp_neg_first_box hq.2.2
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v25 : ℝ := (2 : ℝ)*(Real.exp (-qv.2))
  have h25 : Bounds v25 (1023/512 : ℝ) (2 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v26 : ℝ := v8-v25
  have h26 : Bounds v26 (-2049/1024 : ℝ) (-1023/512 : ℝ) := by
    exact (h8.sub h25).weaken (by norm_num) (by norm_num)
  let v27 : ℝ := v26+(2 : ℝ)
  have h27 : Bounds v27 (-1/1024 : ℝ) (1/512 : ℝ) := by
    exact (h26.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve2 : Bounds (vertexEntropy (Real.exp (-qv.2))) (-1/1024 : ℝ) (1/512 : ℝ) := by
    convert h27 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v8,v25,v26,v27] <;> ring
  exact hve2

theorem coverS1_hg2_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (criticalObservable (Real.exp (-qv.2))) (1023/1024 : ℝ) (513/512 : ℝ) := by
  have hz := exp_neg_first_box hq.2.2
  have he2 := coverS1_he2_bounds hq
  have he2p : Bounds (entropy (Real.exp (-qv.2))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he2.2⟩
  let v28 : ℝ := criticalOmega*(entropy (Real.exp (-qv.2)))
  have h28 : Bounds v28 (0 : ℝ) (1/512 : ℝ) := by
    exact criticalOmega_coarse_bounds.mul_corners he2p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v29 : ℝ := (Real.exp (-qv.2))+v28
  have h29 : Bounds v29 (1023/1024 : ℝ) (513/512 : ℝ) := by
    exact (hz.add h28).weaken (by norm_num) (by norm_num)
  have hg2 : Bounds (criticalObservable (Real.exp (-qv.2))) (1023/1024 : ℝ) (513/512 : ℝ) := by
    convert h29 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v28,v29] <;> ring
  exact hg2

theorem coverS1_hf0_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 0 (logBoxEdges qv) coverS1Vertex0) (99907/128000 : ℝ) (7815000001/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  let v30 : ℝ := (Real.exp (-qv.1.1))+(Real.exp (-qv.1.2))
  have h30 : Bounds v30 (1023/512 : ℝ) (2 : ℝ) := by
    exact (hx.add hy).weaken (by norm_num) (by norm_num)
  let v31 : ℝ := v30+(Real.exp (-qv.2))
  have h31 : Bounds v31 (3069/1024 : ℝ) (3 : ℝ) := by
    exact (h30.add hz).weaken (by norm_num) (by norm_num)
  let v32 : ℝ := v31*(1/3 : ℝ)
  have h32 : Bounds v32 (1023/1024 : ℝ) (1 : ℝ) := by
    exact h31.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v33 : ℝ := v32-(7872292148643627/36028797018963968 : ℝ)
  have h33 : Bounds v33 (99907/128000 : ℝ) (7815000001/10000000000 : ℝ) := by
    exact (h32.sub (Bounds.refl (7872292148643627/36028797018963968 : ℝ))).weaken (by norm_num) (by norm_num)
  have hf0 : Bounds (certificateFeature 0 (logBoxEdges qv) coverS1Vertex0) (99907/128000 : ℝ) (7815000001/10000000000 : ℝ) := by
    convert h33 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v30,v31,v32,v33] <;> ring
  exact hf0

theorem coverS1_hf1_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 1 (logBoxEdges qv) coverS1Vertex0) (1975711609/2000000000 : ℝ) (495391317/500000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  let v34 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.2))
  have h34 : Bounds v34 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v35 : ℝ := v34*(Real.exp (-qv.2))
  have h35 : Bounds v35 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h34.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v36 : ℝ := v35-criticalTriangle
  have h36 : Bounds v36 (1975711609/2000000000 : ℝ) (495391317/500000000 : ℝ) := by
    exact (h35.sub criticalTriangle_checked_bounds).weaken (by norm_num) (by norm_num)
  have hf1 : Bounds (certificateFeature 1 (logBoxEdges qv) coverS1Vertex0) (1975711609/2000000000 : ℝ) (495391317/500000000 : ℝ) := by
    convert h36 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v34,v35,v36] <;> ring
  exact hf1

theorem coverS1_hf2_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 2 (logBoxEdges qv) coverS1Vertex0) (-4610000001/10000000000 : ℝ) (-58883/128000 : ℝ) := by
  have he0 := coverS1_he0_bounds hq
  have he0p : Bounds (entropy (Real.exp (-qv.1.1))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he0.2⟩
  have he1 := coverS1_he1_bounds hq
  have he1p : Bounds (entropy (Real.exp (-qv.1.2))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he1.2⟩
  have he2 := coverS1_he2_bounds hq
  have he2p : Bounds (entropy (Real.exp (-qv.2))) 0 (1/1024 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he2.2⟩
  let v37 : ℝ := (entropy (Real.exp (-qv.1.1)))+(entropy (Real.exp (-qv.1.2)))
  have h37 : Bounds v37 (0 : ℝ) (1/512 : ℝ) := by
    exact (he0p.add he1p).weaken (by norm_num) (by norm_num)
  let v38 : ℝ := v37+(entropy (Real.exp (-qv.2)))
  have h38 : Bounds v38 (0 : ℝ) (3/1024 : ℝ) := by
    exact (h37.add he2p).weaken (by norm_num) (by norm_num)
  let v39 : ℝ := v38*(1/3 : ℝ)
  have h39 : Bounds v39 (0 : ℝ) (1/1024 : ℝ) := by
    exact h38.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v40 : ℝ := v39-(8304637712871195/18014398509481984 : ℝ)
  have h40 : Bounds v40 (-4610000001/10000000000 : ℝ) (-58883/128000 : ℝ) := by
    exact (h39.sub (Bounds.refl (8304637712871195/18014398509481984 : ℝ))).weaken (by norm_num) (by norm_num)
  have hf2 : Bounds (certificateFeature 2 (logBoxEdges qv) coverS1Vertex0) (-4610000001/10000000000 : ℝ) (-58883/128000 : ℝ) := by
    convert h40 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v37,v38,v39,v40] <;> ring
  exact hf2

theorem coverS1_hf3_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 3 (logBoxEdges qv) coverS1Vertex0) (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hmu := coverS1_hmu_bounds hq
  let v41 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h41 : Bounds v41 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v42 : ℝ := v41*(Real.exp (-qv.2))
  have h42 : Bounds v42 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h41.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v43 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v42
  have h43 : Bounds v43 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlx.add h42).weaken (by norm_num) (by norm_num)
  let v44 : ℝ := (1 : ℝ)*v43
  have h44 : Bounds v44 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v45 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h45 : Bounds v45 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v46 : ℝ := v45*(Real.exp (-qv.1.1))
  have h46 : Bounds v46 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h45.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v47 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v46
  have h47 : Bounds v47 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hly.add h46).weaken (by norm_num) (by norm_num)
  let v48 : ℝ := (1 : ℝ)*v47
  have h48 : Bounds v48 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v49 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h49 : Bounds v49 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v50 : ℝ := v49*(Real.exp (-qv.1.2))
  have h50 : Bounds v50 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h49.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v51 : ℝ := (Real.log (Real.exp (-qv.2)))+v50
  have h51 : Bounds v51 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlz.add h50).weaken (by norm_num) (by norm_num)
  let v52 : ℝ := (1 : ℝ)*v51
  have h52 : Bounds v52 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v53 : ℝ := v44+v48
  have h53 : Bounds v53 (43378072739/625000000 : ℝ) (347713218831/5000000000 : ℝ) := by
    exact (h44.add h48).weaken (by norm_num) (by norm_num)
  let v54 : ℝ := v53+v52
  have h54 : Bounds v54 (130134218217/1250000000 : ℝ) (1043139656493/10000000000 : ℝ) := by
    exact (h53.add h52).weaken (by norm_num) (by norm_num)
  let v55 : ℝ := v54*(1/3 : ℝ)
  have h55 : Bounds v55 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h54.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf3 : Bounds (certificateFeature 3 (logBoxEdges qv) coverS1Vertex0) (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    convert h55 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55] <;> ring
  exact hf3

theorem coverS1_hf4_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 4 (logBoxEdges qv) coverS1Vertex0) (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hmu := coverS1_hmu_bounds hq
  let v56 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h56 : Bounds v56 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v57 : ℝ := v56*(Real.exp (-qv.2))
  have h57 : Bounds v57 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h56.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v58 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v57
  have h58 : Bounds v58 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlx.add h57).weaken (by norm_num) (by norm_num)
  let v59 : ℝ := (Real.exp (-qv.1.1))*v58
  have h59 : Bounds v59 (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hx.mul_corners h58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v60 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h60 : Bounds v60 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v61 : ℝ := v60*(Real.exp (-qv.1.1))
  have h61 : Bounds v61 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h60.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v62 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v61
  have h62 : Bounds v62 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hly.add h61).weaken (by norm_num) (by norm_num)
  let v63 : ℝ := (Real.exp (-qv.1.2))*v62
  have h63 : Bounds v63 (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hy.mul_corners h62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v64 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h64 : Bounds v64 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v65 : ℝ := v64*(Real.exp (-qv.1.2))
  have h65 : Bounds v65 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h64.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v66 : ℝ := (Real.log (Real.exp (-qv.2)))+v65
  have h66 : Bounds v66 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlz.add h65).weaken (by norm_num) (by norm_num)
  let v67 : ℝ := (Real.exp (-qv.2))*v66
  have h67 : Bounds v67 (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hz.mul_corners h66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v68 : ℝ := v59+v63
  have h68 : Bounds v68 (173342845359/2500000000 : ℝ) (347713218831/5000000000 : ℝ) := by
    exact (h59.add h63).weaken (by norm_num) (by norm_num)
  let v69 : ℝ := v68+v67
  have h69 : Bounds v69 (520028536077/5000000000 : ℝ) (1043139656493/10000000000 : ℝ) := by
    exact (h68.add h67).weaken (by norm_num) (by norm_num)
  let v70 : ℝ := v69*(1/3 : ℝ)
  have h70 : Bounds v70 (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h69.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf4 : Bounds (certificateFeature 4 (logBoxEdges qv) coverS1Vertex0) (173342845359/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    convert h70 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70] <;> ring
  exact hf4

theorem coverS1_hf5_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 5 (logBoxEdges qv) coverS1Vertex0) (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hmu := coverS1_hmu_bounds hq
  let v71 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h71 : Bounds v71 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v72 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h72 : Bounds v72 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v73 : ℝ := v72*(Real.exp (-qv.2))
  have h73 : Bounds v73 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h72.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v74 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v73
  have h74 : Bounds v74 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlx.add h73).weaken (by norm_num) (by norm_num)
  let v75 : ℝ := v71*v74
  have h75 : Bounds v75 (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h71.mul_corners h74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v76 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h76 : Bounds v76 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v77 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h77 : Bounds v77 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v78 : ℝ := v77*(Real.exp (-qv.1.1))
  have h78 : Bounds v78 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h77.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v79 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v78
  have h79 : Bounds v79 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hly.add h78).weaken (by norm_num) (by norm_num)
  let v80 : ℝ := v76*v79
  have h80 : Bounds v80 (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h76.mul_corners h79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v81 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h81 : Bounds v81 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v82 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h82 : Bounds v82 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v83 : ℝ := v82*(Real.exp (-qv.1.2))
  have h83 : Bounds v83 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h82.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v84 : ℝ := (Real.log (Real.exp (-qv.2)))+v83
  have h84 : Bounds v84 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlz.add h83).weaken (by norm_num) (by norm_num)
  let v85 : ℝ := v81*v84
  have h85 : Bounds v85 (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h81.mul_corners h84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v86 : ℝ := v75+v80
  have h86 : Bounds v86 (21646695653/312500000 : ℝ) (347713218831/5000000000 : ℝ) := by
    exact (h75.add h80).weaken (by norm_num) (by norm_num)
  let v87 : ℝ := v86+v85
  have h87 : Bounds v87 (64940086959/625000000 : ℝ) (1043139656493/10000000000 : ℝ) := by
    exact (h86.add h85).weaken (by norm_num) (by norm_num)
  let v88 : ℝ := v87*(1/3 : ℝ)
  have h88 : Bounds v88 (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h87.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf5 : Bounds (certificateFeature 5 (logBoxEdges qv) coverS1Vertex0) (21646695653/625000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    convert h88 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88] <;> ring
  exact hf5

theorem coverS1_hf6_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 6 (logBoxEdges qv) coverS1Vertex0) (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hmu := coverS1_hmu_bounds hq
  let v89 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h89 : Bounds v89 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v90 : ℝ := v89*(Real.exp (-qv.1.1))
  have h90 : Bounds v90 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h89.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v91 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h91 : Bounds v91 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v92 : ℝ := v91*(Real.exp (-qv.2))
  have h92 : Bounds v92 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h91.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v93 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v92
  have h93 : Bounds v93 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlx.add h92).weaken (by norm_num) (by norm_num)
  let v94 : ℝ := v90*v93
  have h94 : Bounds v94 (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h90.mul_corners h93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v95 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h95 : Bounds v95 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v96 : ℝ := v95*(Real.exp (-qv.1.2))
  have h96 : Bounds v96 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h95.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v97 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h97 : Bounds v97 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v98 : ℝ := v97*(Real.exp (-qv.1.1))
  have h98 : Bounds v98 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h97.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v99 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v98
  have h99 : Bounds v99 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hly.add h98).weaken (by norm_num) (by norm_num)
  let v100 : ℝ := v96*v99
  have h100 : Bounds v100 (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h96.mul_corners h99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v101 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h101 : Bounds v101 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v102 : ℝ := v101*(Real.exp (-qv.2))
  have h102 : Bounds v102 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h101.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v103 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h103 : Bounds v103 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v104 : ℝ := v103*(Real.exp (-qv.1.2))
  have h104 : Bounds v104 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h103.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v105 : ℝ := (Real.log (Real.exp (-qv.2)))+v104
  have h105 : Bounds v105 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlz.add h104).weaken (by norm_num) (by norm_num)
  let v106 : ℝ := v102*v105
  have h106 : Bounds v106 (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h102.mul_corners h105 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v107 : ℝ := v94+v100
  have h107 : Bounds v107 (173004450411/2500000000 : ℝ) (347713218831/5000000000 : ℝ) := by
    exact (h94.add h100).weaken (by norm_num) (by norm_num)
  let v108 : ℝ := v107+v106
  have h108 : Bounds v108 (519013351233/5000000000 : ℝ) (1043139656493/10000000000 : ℝ) := by
    exact (h107.add h106).weaken (by norm_num) (by norm_num)
  let v109 : ℝ := v108*(1/3 : ℝ)
  have h109 : Bounds v109 (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h108.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf6 : Bounds (certificateFeature 6 (logBoxEdges qv) coverS1Vertex0) (173004450411/5000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    convert h109 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109] <;> ring
  exact hf6

theorem coverS1_hf7_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 7 (logBoxEdges qv) coverS1Vertex0) (-339563691/10000000000 : ℝ) (0 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hmu := coverS1_hmu_bounds hq
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v110 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h110 : Bounds v110 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v111 : ℝ := v110*(Real.exp (-qv.2))
  have h111 : Bounds v111 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h110.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v112 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v111
  have h112 : Bounds v112 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlx.add h111).weaken (by norm_num) (by norm_num)
  let v113 : ℝ := v6*v112
  have h113 : Bounds v113 (-339563691/10000000000 : ℝ) (0 : ℝ) := by
    exact h6.mul_corners h112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v114 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h114 : Bounds v114 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v115 : ℝ := v114*(Real.exp (-qv.1.1))
  have h115 : Bounds v115 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h114.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v116 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v115
  have h116 : Bounds v116 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hly.add h115).weaken (by norm_num) (by norm_num)
  let v117 : ℝ := v7*v116
  have h117 : Bounds v117 (-339563691/10000000000 : ℝ) (0 : ℝ) := by
    exact h7.mul_corners h116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v118 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h118 : Bounds v118 (347373579549/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v119 : ℝ := v118*(Real.exp (-qv.1.2))
  have h119 : Bounds v119 (347034347537/10000000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact h118.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v120 : ℝ := (Real.log (Real.exp (-qv.2)))+v119
  have h120 : Bounds v120 (43378072739/1250000000 : ℝ) (347713218831/10000000000 : ℝ) := by
    exact (hlz.add h119).weaken (by norm_num) (by norm_num)
  let v121 : ℝ := v8*v120
  have h121 : Bounds v121 (-339563691/10000000000 : ℝ) (0 : ℝ) := by
    exact h8.mul_corners h120 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v122 : ℝ := v113+v117
  have h122 : Bounds v122 (-339563691/5000000000 : ℝ) (0 : ℝ) := by
    exact (h113.add h117).weaken (by norm_num) (by norm_num)
  let v123 : ℝ := v122+v121
  have h123 : Bounds v123 (-1018691073/10000000000 : ℝ) (0 : ℝ) := by
    exact (h122.add h121).weaken (by norm_num) (by norm_num)
  let v124 : ℝ := v123*(1/3 : ℝ)
  have h124 : Bounds v124 (-339563691/10000000000 : ℝ) (0 : ℝ) := by
    exact h123.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf7 : Bounds (certificateFeature 7 (logBoxEdges qv) coverS1Vertex0) (-339563691/10000000000 : ℝ) (0 : ℝ) := by
    convert h124 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v7,v8,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124] <;> ring
  exact hf7

theorem coverS1_hf8_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 8 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hk := coverS1_hk_bounds hq
  have hve0 := coverS1_hve0_bounds hq
  have hve1 := coverS1_hve1_bounds hq
  have hve2 := coverS1_hve2_bounds hq
  let v125 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h125 : Bounds v125 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v126 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h126 : Bounds v126 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v127 : ℝ := v125-v126
  have h127 : Bounds v127 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h125.sub h126).weaken (by norm_num) (by norm_num)
  let v128 : ℝ := (Real.exp (-qv.1.1))*v127
  have h128 : Bounds v128 (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
    exact hx.mul_corners h127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v129 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h129 : Bounds v129 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v130 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h130 : Bounds v130 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v131 : ℝ := v129-v130
  have h131 : Bounds v131 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h129.sub h130).weaken (by norm_num) (by norm_num)
  let v132 : ℝ := (Real.exp (-qv.1.2))*v131
  have h132 : Bounds v132 (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
    exact hy.mul_corners h131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v133 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h133 : Bounds v133 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v134 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h134 : Bounds v134 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v135 : ℝ := v133-v134
  have h135 : Bounds v135 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h133.sub h134).weaken (by norm_num) (by norm_num)
  let v136 : ℝ := (Real.exp (-qv.2))*v135
  have h136 : Bounds v136 (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
    exact hz.mul_corners h135 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v137 : ℝ := v128+v132
  have h137 : Bounds v137 (-12434765627/2500000000 : ℝ) (-6196677017/1250000000 : ℝ) := by
    exact (h128.add h132).weaken (by norm_num) (by norm_num)
  let v138 : ℝ := v137+v136
  have h138 : Bounds v138 (-37304296881/5000000000 : ℝ) (-18590031051/2500000000 : ℝ) := by
    exact (h137.add h136).weaken (by norm_num) (by norm_num)
  let v139 : ℝ := v138*(1/3 : ℝ)
  have h139 : Bounds v139 (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
    exact h138.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf8 : Bounds (certificateFeature 8 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-6196677017/2500000000 : ℝ) := by
    convert h139 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139] <;> ring
  exact hf8

theorem coverS1_hf9_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 9 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hk := coverS1_hk_bounds hq
  have hve0 := coverS1_hve0_bounds hq
  have hve1 := coverS1_hve1_bounds hq
  have hve2 := coverS1_hve2_bounds hq
  let v140 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h140 : Bounds v140 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v141 : ℝ := v140*(Real.exp (-qv.1.1))
  have h141 : Bounds v141 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h140.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v142 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h142 : Bounds v142 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v143 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h143 : Bounds v143 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v144 : ℝ := v142-v143
  have h144 : Bounds v144 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h142.sub h143).weaken (by norm_num) (by norm_num)
  let v145 : ℝ := v141*v144
  have h145 : Bounds v145 (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
    exact h141.mul_corners h144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v146 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h146 : Bounds v146 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v147 : ℝ := v146*(Real.exp (-qv.1.2))
  have h147 : Bounds v147 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h146.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v148 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h148 : Bounds v148 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v149 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h149 : Bounds v149 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v150 : ℝ := v148-v149
  have h150 : Bounds v150 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h148.sub h149).weaken (by norm_num) (by norm_num)
  let v151 : ℝ := v147*v150
  have h151 : Bounds v151 (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
    exact h147.mul_corners h150 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v152 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h152 : Bounds v152 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v153 : ℝ := v152*(Real.exp (-qv.2))
  have h153 : Bounds v153 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h152.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v154 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h154 : Bounds v154 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v155 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h155 : Bounds v155 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v156 : ℝ := v154-v155
  have h156 : Bounds v156 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h154.sub h155).weaken (by norm_num) (by norm_num)
  let v157 : ℝ := v153*v156
  have h157 : Bounds v157 (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
    exact h153.mul_corners h156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v158 : ℝ := v145+v151
  have h158 : Bounds v158 (-12434765627/2500000000 : ℝ) (-4947664033/1000000000 : ℝ) := by
    exact (h145.add h151).weaken (by norm_num) (by norm_num)
  let v159 : ℝ := v158+v157
  have h159 : Bounds v159 (-37304296881/5000000000 : ℝ) (-14842992099/2000000000 : ℝ) := by
    exact (h158.add h157).weaken (by norm_num) (by norm_num)
  let v160 : ℝ := v159*(1/3 : ℝ)
  have h160 : Bounds v160 (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
    exact h159.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf9 : Bounds (certificateFeature 9 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-4947664033/2000000000 : ℝ) := by
    convert h160 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160] <;> ring
  exact hf9

theorem coverS1_hf10_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 10 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hk := coverS1_hk_bounds hq
  have hve0 := coverS1_hve0_bounds hq
  have hve1 := coverS1_hve1_bounds hq
  have hve2 := coverS1_hve2_bounds hq
  let v161 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h161 : Bounds v161 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v162 : ℝ := v161*(Real.exp (-qv.1.1))
  have h162 : Bounds v162 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h161.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v163 : ℝ := v162*(Real.exp (-qv.1.1))
  have h163 : Bounds v163 (4980497341/5000000000 : ℝ) (1 : ℝ) := by
    exact h162.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v164 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h164 : Bounds v164 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v165 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h165 : Bounds v165 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v166 : ℝ := v164-v165
  have h166 : Bounds v166 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h164.sub h165).weaken (by norm_num) (by norm_num)
  let v167 : ℝ := v163*v166
  have h167 : Bounds v167 (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
    exact h163.mul_corners h166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v168 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h168 : Bounds v168 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v169 : ℝ := v168*(Real.exp (-qv.1.2))
  have h169 : Bounds v169 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h168.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v170 : ℝ := v169*(Real.exp (-qv.1.2))
  have h170 : Bounds v170 (4980497341/5000000000 : ℝ) (1 : ℝ) := by
    exact h169.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v171 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h171 : Bounds v171 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v172 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h172 : Bounds v172 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v173 : ℝ := v171-v172
  have h173 : Bounds v173 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h171.sub h172).weaken (by norm_num) (by norm_num)
  let v174 : ℝ := v170*v173
  have h174 : Bounds v174 (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
    exact h170.mul_corners h173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v175 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h175 : Bounds v175 (4990239143/5000000000 : ℝ) (1 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v176 : ℝ := v175*(Real.exp (-qv.2))
  have h176 : Bounds v176 (398829269/400000000 : ℝ) (1 : ℝ) := by
    exact h175.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v177 : ℝ := v176*(Real.exp (-qv.2))
  have h177 : Bounds v177 (4980497341/5000000000 : ℝ) (1 : ℝ) := by
    exact h176.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v178 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h178 : Bounds v178 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v179 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h179 : Bounds v179 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v180 : ℝ := v178-v179
  have h180 : Bounds v180 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h178.sub h179).weaken (by norm_num) (by norm_num)
  let v181 : ℝ := v177*v180
  have h181 : Bounds v181 (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
    exact h177.mul_corners h180 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v182 : ℝ := v167+v174
  have h182 : Bounds v182 (-12434765627/2500000000 : ℝ) (-24714161649/5000000000 : ℝ) := by
    exact (h167.add h174).weaken (by norm_num) (by norm_num)
  let v183 : ℝ := v182+v181
  have h183 : Bounds v183 (-37304296881/5000000000 : ℝ) (-74142484947/10000000000 : ℝ) := by
    exact (h182.add h181).weaken (by norm_num) (by norm_num)
  let v184 : ℝ := v183*(1/3 : ℝ)
  have h184 : Bounds v184 (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
    exact h183.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf10 : Bounds (certificateFeature 10 (logBoxEdges qv) coverS1Vertex0) (-12434765627/5000000000 : ℝ) (-24714161649/10000000000 : ℝ) := by
    convert h184 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184] <;> ring
  exact hf10

theorem coverS1_hf11_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateFeature 11 (logBoxEdges qv) coverS1Vertex0) (0 : ℝ) (6071663/2500000000 : ℝ) := by
  have hx := exp_neg_first_box hq.1
  have hy := exp_neg_first_box hq.2.1
  have hz := exp_neg_first_box hq.2.2
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.1) (-1/1024) 0 from
      ⟨by linarith [hq.1.2],neg_nonpos.mpr hq.1.1⟩)
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.1.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.1.2],neg_nonpos.mpr hq.2.1.1⟩)
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/1024) 0 := by
    simpa only [Real.log_exp] using (show Bounds (-qv.2) (-1/1024) 0 from
      ⟨by linarith [hq.2.2.2],neg_nonpos.mpr hq.2.2.1⟩)
  have hk := coverS1_hk_bounds hq
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-1/1024 : ℝ) (0 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hve0 := coverS1_hve0_bounds hq
  have hve1 := coverS1_hve1_bounds hq
  have hve2 := coverS1_hve2_bounds hq
  let v185 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h185 : Bounds v185 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v186 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h186 : Bounds v186 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v187 : ℝ := v185-v186
  have h187 : Bounds v187 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h185.sub h186).weaken (by norm_num) (by norm_num)
  let v188 : ℝ := v6*v187
  have h188 : Bounds v188 (0 : ℝ) (6071663/2500000000 : ℝ) := by
    exact h6.mul_corners h187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v189 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h189 : Bounds v189 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v190 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h190 : Bounds v190 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v191 : ℝ := v189-v190
  have h191 : Bounds v191 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h189.sub h190).weaken (by norm_num) (by norm_num)
  let v192 : ℝ := v7*v191
  have h192 : Bounds v192 (0 : ℝ) (6071663/2500000000 : ℝ) := by
    exact h7.mul_corners h191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v193 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h193 : Bounds v193 (-1/512 : ℝ) (1/256 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v194 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h194 : Bounds v194 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v195 : ℝ := v193-v194
  have h195 : Bounds v195 (-12434765627/5000000000 : ℝ) (-15879/6400 : ℝ) := by
    exact (h193.sub h194).weaken (by norm_num) (by norm_num)
  let v196 : ℝ := v8*v195
  have h196 : Bounds v196 (0 : ℝ) (6071663/2500000000 : ℝ) := by
    exact h8.mul_corners h195 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v197 : ℝ := v188+v192
  have h197 : Bounds v197 (0 : ℝ) (6071663/1250000000 : ℝ) := by
    exact (h188.add h192).weaken (by norm_num) (by norm_num)
  let v198 : ℝ := v197+v196
  have h198 : Bounds v198 (0 : ℝ) (18214989/2500000000 : ℝ) := by
    exact (h197.add h196).weaken (by norm_num) (by norm_num)
  let v199 : ℝ := v198*(1/3 : ℝ)
  have h199 : Bounds v199 (0 : ℝ) (6071663/2500000000 : ℝ) := by
    exact h198.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf11 : Bounds (certificateFeature 11 (logBoxEdges qv) coverS1Vertex0) (0 : ℝ) (6071663/2500000000 : ℝ) := by
    convert h199 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v7,v8,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199] <;> ring
  exact hf11

theorem coverS1_hH_bounds {qv : EdgeTriple} (hq : qv ∈ logCube (1/1024)) :
    Bounds (certificateHoeffding (logBoxEdges qv) coverS1Vertex0) (-9620300509/10000000000 : ℝ) (1542773289/5000000000 : ℝ) := by
  have hg0 := coverS1_hg0_bounds hq
  have hg1 := coverS1_hg1_bounds hq
  have hg2 := coverS1_hg2_bounds hq
  let v200 : ℝ := (criticalObservable (Real.exp (-qv.1.1)))*(criticalObservable (Real.exp (-qv.1.1)))
  have h200 : Bounds v200 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg0.mul_corners hg0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v201 : ℝ := (criticalObservable (Real.exp (-qv.1.2)))*(criticalObservable (Real.exp (-qv.1.2)))
  have h201 : Bounds v201 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg1.mul_corners hg1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v202 : ℝ := (criticalObservable (Real.exp (-qv.2)))*(criticalObservable (Real.exp (-qv.2)))
  have h202 : Bounds v202 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg2.mul_corners hg2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v203 : ℝ := v200+v201
  have h203 : Bounds v203 (4990239143/2500000000 : ℝ) (10039100647/5000000000 : ℝ) := by
    exact (h200.add h201).weaken (by norm_num) (by norm_num)
  let v204 : ℝ := v203+v202
  have h204 : Bounds v204 (14970717429/5000000000 : ℝ) (30117301941/10000000000 : ℝ) := by
    exact (h203.add h202).weaken (by norm_num) (by norm_num)
  let v205 : ℝ := v204*(1/3 : ℝ)
  have h205 : Bounds v205 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact h204.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v206 : ℝ := (criticalObservable (Real.exp (-qv.1.1)))*(criticalObservable (Real.exp (-qv.1.2)))
  have h206 : Bounds v206 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg0.mul_corners hg1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v207 : ℝ := (criticalObservable (Real.exp (-qv.1.2)))*(criticalObservable (Real.exp (-qv.2)))
  have h207 : Bounds v207 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg1.mul_corners hg2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v208 : ℝ := (criticalObservable (Real.exp (-qv.2)))*(criticalObservable (Real.exp (-qv.1.1)))
  have h208 : Bounds v208 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact hg2.mul_corners hg0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v209 : ℝ := v206+v207
  have h209 : Bounds v209 (4990239143/2500000000 : ℝ) (10039100647/5000000000 : ℝ) := by
    exact (h206.add h207).weaken (by norm_num) (by norm_num)
  let v210 : ℝ := v209+v208
  have h210 : Bounds v210 (14970717429/5000000000 : ℝ) (30117301941/10000000000 : ℝ) := by
    exact (h209.add h208).weaken (by norm_num) (by norm_num)
  let v211 : ℝ := v210*(1/3 : ℝ)
  have h211 : Bounds v211 (4990239143/5000000000 : ℝ) (10039100647/10000000000 : ℝ) := by
    exact h210.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v212 : ℝ := (2 : ℝ)*v211
  have h212 : Bounds v212 (4990239143/2500000000 : ℝ) (10039100647/5000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners h211 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v213 : ℝ := v205-v212
  have h213 : Bounds v213 (-78888461/78125000 : ℝ) (-396874237/400000000 : ℝ) := by
    exact (h205.sub h212).weaken (by norm_num) (by norm_num)
  let v214 : ℝ := criticalOmega*(8304637712871195/18014398509481984 : ℝ)
  have h214 : Bounds v214 (0 : ℝ) (9220000001/10000000000 : ℝ) := by
    exact criticalOmega_coarse_bounds.mul_corners (Bounds.refl (8304637712871195/18014398509481984 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v215 : ℝ := (7872292148643627/36028797018963968 : ℝ)+v214
  have h215 : Bounds v215 (2184999999/10000000000 : ℝ) (11405000001/10000000000 : ℝ) := by
    exact ((Bounds.refl (7872292148643627/36028797018963968 : ℝ)).add h214).weaken (by norm_num) (by norm_num)
  let v216 : ℝ := v215*v215
  have h216 : Bounds v216 (477422499/10000000000 : ℝ) (13007402503/10000000000 : ℝ) := by
    exact h215.mul_corners h215 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v217 : ℝ := v213+v216
  have h217 : Bounds v217 (-9620300509/10000000000 : ℝ) (1542773289/5000000000 : ℝ) := by
    exact (h213.add h216).weaken (by norm_num) (by norm_num)
  have hH : Bounds (certificateHoeffding (logBoxEdges qv) coverS1Vertex0) (-9620300509/10000000000 : ℝ) (1542773289/5000000000 : ℝ) := by
    convert h217 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217] <;> ring
  exact hH

/-- A checked bound on a genuine non-apex certificate throughout a 3D box.
This certifies one subdomain, not the complete S1 cube or twelve-cell cover. -/
theorem coverS1_vertex0_first_box {qv : EdgeTriple}
    (hq : qv ∈ logCube (1/1024)) :
    3 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by
  have hf0 := coverS1_hf0_bounds hq
  have hf1 := coverS1_hf1_bounds hq
  have hf2 := coverS1_hf2_bounds hq
  have hf3 := coverS1_hf3_bounds hq
  have hf4 := coverS1_hf4_bounds hq
  have hf5 := coverS1_hf5_bounds hq
  have hf6 := coverS1_hf6_bounds hq
  have hf7 := coverS1_hf7_bounds hq
  have hf8 := coverS1_hf8_bounds hq
  have hf9 := coverS1_hf9_bounds hq
  have hf10 := coverS1_hf10_bounds hq
  have hf11 := coverS1_hf11_bounds hq
  have hH := coverS1_hH_bounds hq
  let v218 : ℝ := (8639019645839429/9007199254740992 : ℝ)*(certificateFeature 0 (logBoxEdges qv) coverS1Vertex0)
  have h218 : Bounds v218 (374309323/500000000 : ℝ) (3747776453/5000000000 : ℝ) := by
    exact (Bounds.refl (8639019645839429/9007199254740992 : ℝ)).mul_corners hf0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v219 : ℝ := (-2657272677596523/562949953421312 : ℝ)*(certificateFeature 1 (logBoxEdges qv) coverS1Vertex0)
  have h219 : Bounds v219 (-730743139/156250000 : ℝ) (-46629406801/10000000000 : ℝ) := by
    exact (Bounds.refl (-2657272677596523/562949953421312 : ℝ)).mul_corners hf1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v220 : ℝ := (140737488299033/140737488355328 : ℝ)*(certificateFeature 2 (logBoxEdges qv) coverS1Vertex0)
  have h220 : Bounds v220 (-461/1000 : ℝ) (-4600234373/10000000000 : ℝ) := by
    exact (Bounds.refl (140737488299033/140737488355328 : ℝ)).mul_corners hf2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v221 : ℝ := (-7541973450629039/36893488147419103232 : ℝ)*(certificateFeature 3 (logBoxEdges qv) coverS1Vertex0)
  have h221 : Bounds v221 (-17770371/2500000000 : ℝ) (-17735177/2500000000 : ℝ) := by
    exact (Bounds.refl (-7541973450629039/36893488147419103232 : ℝ)).mul_corners hf3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v222 : ℝ := (-8604084221028639/72057594037927936 : ℝ)*(certificateFeature 4 (logBoxEdges qv) coverS1Vertex0)
  have h222 : Bounds v222 (-20759462341/5000000000 : ℝ) (-41396232013/10000000000 : ℝ) := by
    exact (Bounds.refl (-8604084221028639/72057594037927936 : ℝ)).mul_corners hf4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v223 : ℝ := (1019507261509151/1125899906842624 : ℝ)*(certificateFeature 5 (logBoxEdges qv) coverS1Vertex0)
  have h223 : Bounds v223 (78404708169/2500000000 : ℝ) (9839244739/312500000 : ℝ) := by
    exact (Bounds.refl (1019507261509151/1125899906842624 : ℝ)).mul_corners hf5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v224 : ℝ := (-7199522257880297/9007199254740992 : ℝ)*(certificateFeature 6 (logBoxEdges qv) coverS1Vertex0)
  have h224 : Bounds v224 (-27792979677/1000000000 : ℝ) (-138283761269/5000000000 : ℝ) := by
    exact (Bounds.refl (-7199522257880297/9007199254740992 : ℝ)).mul_corners hf6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v225 : ℝ := (8774057038934945/72057594037927936 : ℝ)*(certificateFeature 7 (logBoxEdges qv) coverS1Vertex0)
  have h225 : Bounds v225 (-10336701/2500000000 : ℝ) (0 : ℝ) := by
    exact (Bounds.refl (8774057038934945/72057594037927936 : ℝ)).mul_corners hf7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v226 : ℝ := (-2521529215217977/18014398509481984 : ℝ)*(certificateFeature 8 (logBoxEdges qv) coverS1Vertex0)
  have h226 : Bounds v226 (346946963/1000000000 : ℝ) (43513283/125000000 : ℝ) := by
    exact (Bounds.refl (-2521529215217977/18014398509481984 : ℝ)).mul_corners hf8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v227 : ℝ := (7097966112403971/18014398509481984 : ℝ)*(certificateFeature 9 (logBoxEdges qv) coverS1Vertex0)
  have h227 : Bounds v227 (-9798999949/10000000000 : ℝ) (-2436825161/2500000000 : ℝ) := by
    exact (Bounds.refl (7097966112403971/18014398509481984 : ℝ)).mul_corners hf9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v228 : ℝ := (-6881924343606227/9007199254740992 : ℝ)*(certificateFeature 10 (logBoxEdges qv) coverS1Vertex0)
  have h228 : Bounds v228 (1888278319/1000000000 : ℝ) (3800298577/2000000000 : ℝ) := by
    exact (Bounds.refl (-6881924343606227/9007199254740992 : ℝ)).mul_corners hf10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v229 : ℝ := (3354424007516313/4503599627370496 : ℝ)*(certificateFeature 11 (logBoxEdges qv) coverS1Vertex0)
  have h229 : Bounds v229 (0 : ℝ) (1808947/1000000000 : ℝ) := by
    exact (Bounds.refl (3354424007516313/4503599627370496 : ℝ)).mul_corners hf11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v230 : ℝ := v229+(0 : ℝ)
  have h230 : Bounds v230 (0 : ℝ) (1808947/1000000000 : ℝ) := by
    exact (h229.add (Bounds.refl (0 : ℝ))).weaken (by norm_num) (by norm_num)
  let v231 : ℝ := v228+v230
  have h231 : Bounds v231 (1888278319/1000000000 : ℝ) (3803916471/2000000000 : ℝ) := by
    exact (h228.add h230).weaken (by norm_num) (by norm_num)
  let v232 : ℝ := v227+v231
  have h232 : Bounds v232 (9083783241/10000000000 : ℝ) (9272281711/10000000000 : ℝ) := by
    exact (h227.add h231).weaken (by norm_num) (by norm_num)
  let v233 : ℝ := v226+v232
  have h233 : Bounds v233 (12553252871/10000000000 : ℝ) (12753344351/10000000000 : ℝ) := by
    exact (h226.add h232).weaken (by norm_num) (by norm_num)
  let v234 : ℝ := v225+v233
  have h234 : Bounds v234 (12511906067/10000000000 : ℝ) (12753344351/10000000000 : ℝ) := by
    exact (h225.add h233).weaken (by norm_num) (by norm_num)
  let v235 : ℝ := v224+v234
  have h235 : Bounds v235 (-265417890703/10000000000 : ℝ) (-263814178187/10000000000 : ℝ) := by
    exact (h224.add h234).weaken (by norm_num) (by norm_num)
  let v236 : ℝ := v223+v235
  have h236 : Bounds v236 (48200941973/10000000000 : ℝ) (51041653461/10000000000 : ℝ) := by
    exact (h223.add h235).weaken (by norm_num) (by norm_num)
  let v237 : ℝ := v222+v236
  have h237 : Bounds v237 (6682017291/10000000000 : ℝ) (1205677681/1250000000 : ℝ) := by
    exact (h222.add h236).weaken (by norm_num) (by norm_num)
  let v238 : ℝ := v221+v237
  have h238 : Bounds v238 (6610935807/10000000000 : ℝ) (478724037/500000000 : ℝ) := by
    exact (h221.add h237).weaken (by norm_num) (by norm_num)
  let v239 : ℝ := v220+v238
  have h239 : Bounds v239 (2000935807/10000000000 : ℝ) (4974246367/10000000000 : ℝ) := by
    exact (h220.add h238).weaken (by norm_num) (by norm_num)
  let v240 : ℝ := v219+v239
  have h240 : Bounds v240 (-44766625089/10000000000 : ℝ) (-20827580217/5000000000 : ℝ) := by
    exact (h219.add h239).weaken (by norm_num) (by norm_num)
  let v241 : ℝ := v218+v240
  have h241 : Bounds v241 (-37280438629/10000000000 : ℝ) (-4269950941/1250000000 : ℝ) := by
    exact (h218.add h240).weaken (by norm_num) (by norm_num)
  let v242 : ℝ := (0 : ℝ)-v241
  have h242 : Bounds v242 (4269950941/1250000000 : ℝ) (37280438629/10000000000 : ℝ) := by
    exact ((Bounds.refl (0 : ℝ)).sub h241).weaken (by norm_num) (by norm_num)
  let v243 : ℝ := (1080863910568919/1125899906842624 : ℝ)*(certificateHoeffding (logBoxEdges qv) coverS1Vertex0)
  have h243 : Bounds v243 (-9235488489/10000000000 : ℝ) (592424943/2000000000 : ℝ) := by
    exact (Bounds.refl (1080863910568919/1125899906842624 : ℝ)).mul_corners hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v244 : ℝ := v242-v243
  have h244 : Bounds v244 (31197482813/10000000000 : ℝ) (23257963559/5000000000 : ℝ) := by
    exact (h242.sub h243).weaken (by norm_num) (by norm_num)
  have heq : v244 = logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by
    dsimp only [v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244]
    rw [logCertificate,coverCertificate_fin12_expansion]
    simp only [coverS1Theta,coverS1Lam,Matrix.cons_val]
    ring
  rw [heq] at h244
  exact lt_of_lt_of_le (by norm_num) h244.1

/-- The checked box is a subdomain of the actual S1 logarithmic support cube. -/
theorem coverS1_first_box_subset : logCube (1/1024) ⊆ logCube coverS1Q := by
  rintro q ⟨hx,hy,hz⟩
  have hQ : (1/1024 : ℝ) ≤ coverS1Q := by norm_num [coverS1Q]
  exact ⟨⟨hx.1,hx.2.trans hQ⟩,⟨hy.1,hy.2.trans hQ⟩,⟨hz.1,hz.2.trans hQ⟩⟩

/-- The actual S1 certificate is uniformly positive near (1,1,1), expressed
in the original edge coordinates. The full support cube is much larger. -/
theorem coverS1_vertex0_near_one :
    ∀ u ∈ edgeCube (Real.exp (-(1/1024 : ℝ))),
      3 ≤ coverCertificate coverS1Theta coverS1Lam u coverS1Vertex0 := by
  apply coverCertificate_bound_of_orderedLog
  intro q hq
  exact le_of_lt (coverS1_vertex0_first_box (orderedLogDomain_subset_cube _ hq))


end SparseLowerTail.Section05
