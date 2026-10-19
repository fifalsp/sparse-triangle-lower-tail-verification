import SparseLowerTail.Section05.CoverS1FirstBox
import SparseLowerTail.Section05.BoxExponentialBounds

/-! Generated proof-producing S1 subdomain certificate, stable anchor `prop:cover`.
This is one leaf region, not the complete cover. The coefficients and parameter
vertex are the exact S1 data defined in CoverS1FirstBox. -/
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
def coverS1Near1Box : LogBox := ⟨![(0 : ℚ),(0 : ℚ),(1/64 : ℚ)],![(1/64 : ℚ),(1/64 : ℚ),(1/32 : ℚ)]⟩

theorem coverS1Near1_hmu_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (relaxationMultiplier coverS1Vertex0) (347713185379/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
  let v1 : ℝ := (1 : ℝ)-(8304637712871195/18014398509481984 : ℝ)
  have h1 : Bounds v1 (5389999999/10000000000 : ℝ) (539/1000 : ℝ) := by
    exact ((Bounds.refl (1 : ℝ)).sub (Bounds.refl (8304637712871195/18014398509481984 : ℝ))).weaken (by norm_num) (by norm_num)
  let v2 : ℝ := v1-(7872292148643627/36028797018963968 : ℝ)
  have h2 : Bounds v2 (3204999999/10000000000 : ℝ) (3205000001/10000000000 : ℝ) := by
    exact (h1.sub (Bounds.refl (7872292148643627/36028797018963968 : ℝ))).weaken (by norm_num) (by norm_num)
  let v3 : ℝ := v2/criticalTriangle
  have h3 : Bounds v3 (347713185379/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact (h2.div_pos criticalTriangle_sharp_bounds (by norm_num) (by norm_num)).weaken (by norm_num) (by norm_num)
  have hmu : Bounds (relaxationMultiplier coverS1Vertex0) (347713185379/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    convert h3 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v1,v2,v3] <;> ring
  exact hmu

theorem coverS1Near1_hk_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
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

theorem coverS1Near1_he0_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (entropy (Real.exp (-qv.1.1))) (-1/64 : ℝ) (1/64 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/64 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v9 : ℝ := v6-(Real.exp (-qv.1.1))
  have h9 : Bounds v9 (-65/64 : ℝ) (-63/64 : ℝ) := by
    exact (h6.sub hx).weaken (by norm_num) (by norm_num)
  let v10 : ℝ := v9+(1 : ℝ)
  have h10 : Bounds v10 (-1/64 : ℝ) (1/64 : ℝ) := by
    exact (h9.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he0 : Bounds (entropy (Real.exp (-qv.1.1))) (-1/64 : ℝ) (1/64 : ℝ) := by
    convert h10 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v9,v10] <;> ring
  exact he0

theorem coverS1Near1_hve0_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (vertexEntropy (Real.exp (-qv.1.1))) (-1/64 : ℝ) (1/32 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/64 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v11 : ℝ := (2 : ℝ)*(Real.exp (-qv.1.1))
  have h11 : Bounds v11 (63/32 : ℝ) (2 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v12 : ℝ := v6-v11
  have h12 : Bounds v12 (-129/64 : ℝ) (-63/32 : ℝ) := by
    exact (h6.sub h11).weaken (by norm_num) (by norm_num)
  let v13 : ℝ := v12+(2 : ℝ)
  have h13 : Bounds v13 (-1/64 : ℝ) (1/32 : ℝ) := by
    exact (h12.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve0 : Bounds (vertexEntropy (Real.exp (-qv.1.1))) (-1/64 : ℝ) (1/32 : ℝ) := by
    convert h13 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v11,v12,v13] <;> ring
  exact hve0

theorem coverS1Near1_hg0_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (criticalObservable (Real.exp (-qv.1.1))) (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have he0 := coverS1Near1_he0_bounds hq
  have he0p : Bounds (entropy (Real.exp (-qv.1.1))) 0 (1/64 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he0.2⟩
  let v14 : ℝ := criticalOmega*(entropy (Real.exp (-qv.1.1)))
  have h14 : Bounds v14 (0 : ℝ) (72118859/5000000000 : ℝ) := by
    exact criticalOmega_checked_bounds.mul_corners he0p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v15 : ℝ := (Real.exp (-qv.1.1))+v14
  have h15 : Bounds v15 (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
    exact (hx.add h14).weaken (by norm_num) (by norm_num)
  have hg0 : Bounds (criticalObservable (Real.exp (-qv.1.1))) (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
    convert h15 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v14,v15] <;> ring
  exact hg0

theorem coverS1Near1_he1_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (entropy (Real.exp (-qv.1.2))) (-1/64 : ℝ) (1/64 : ℝ) := by
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/64 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v16 : ℝ := v7-(Real.exp (-qv.1.2))
  have h16 : Bounds v16 (-65/64 : ℝ) (-63/64 : ℝ) := by
    exact (h7.sub hy).weaken (by norm_num) (by norm_num)
  let v17 : ℝ := v16+(1 : ℝ)
  have h17 : Bounds v17 (-1/64 : ℝ) (1/64 : ℝ) := by
    exact (h16.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he1 : Bounds (entropy (Real.exp (-qv.1.2))) (-1/64 : ℝ) (1/64 : ℝ) := by
    convert h17 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v7,v16,v17] <;> ring
  exact he1

theorem coverS1Near1_hve1_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (vertexEntropy (Real.exp (-qv.1.2))) (-1/64 : ℝ) (1/32 : ℝ) := by
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/64 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v18 : ℝ := (2 : ℝ)*(Real.exp (-qv.1.2))
  have h18 : Bounds v18 (63/32 : ℝ) (2 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v19 : ℝ := v7-v18
  have h19 : Bounds v19 (-129/64 : ℝ) (-63/32 : ℝ) := by
    exact (h7.sub h18).weaken (by norm_num) (by norm_num)
  let v20 : ℝ := v19+(2 : ℝ)
  have h20 : Bounds v20 (-1/64 : ℝ) (1/32 : ℝ) := by
    exact (h19.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve1 : Bounds (vertexEntropy (Real.exp (-qv.1.2))) (-1/64 : ℝ) (1/32 : ℝ) := by
    convert h20 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v7,v18,v19,v20] <;> ring
  exact hve1

theorem coverS1Near1_hg1_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (criticalObservable (Real.exp (-qv.1.2))) (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have he1 := coverS1Near1_he1_bounds hq
  have he1p : Bounds (entropy (Real.exp (-qv.1.2))) 0 (1/64 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he1.2⟩
  let v21 : ℝ := criticalOmega*(entropy (Real.exp (-qv.1.2)))
  have h21 : Bounds v21 (0 : ℝ) (72118859/5000000000 : ℝ) := by
    exact criticalOmega_checked_bounds.mul_corners he1p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v22 : ℝ := (Real.exp (-qv.1.2))+v21
  have h22 : Bounds v22 (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
    exact (hy.add h21).weaken (by norm_num) (by norm_num)
  have hg1 : Bounds (criticalObservable (Real.exp (-qv.1.2))) (63/64 : ℝ) (5072118859/5000000000 : ℝ) := by
    convert h22 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v21,v22] <;> ring
  exact hg1

theorem coverS1Near1_he2_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (entropy (Real.exp (-qv.2))) (-30769231/2000000000 : ℝ) (161132813/10000000000 : ℝ) := by
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-76923077/2500000000 : ℝ) (-151367187/10000000000 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v23 : ℝ := v8-(Real.exp (-qv.2))
  have h23 : Bounds v23 (-2030769231/2000000000 : ℝ) (-9838867187/10000000000 : ℝ) := by
    exact (h8.sub hz).weaken (by norm_num) (by norm_num)
  let v24 : ℝ := v23+(1 : ℝ)
  have h24 : Bounds v24 (-30769231/2000000000 : ℝ) (161132813/10000000000 : ℝ) := by
    exact (h23.add (Bounds.refl (1 : ℝ))).weaken (by norm_num) (by norm_num)
  have he2 : Bounds (entropy (Real.exp (-qv.2))) (-30769231/2000000000 : ℝ) (161132813/10000000000 : ℝ) := by
    convert h24 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v8,v23,v24] <;> ring
  exact he2

theorem coverS1Near1_hve2_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (vertexEntropy (Real.exp (-qv.2))) (-1/10000000000 : ℝ) (473632813/10000000000 : ℝ) := by
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-76923077/2500000000 : ℝ) (-151367187/10000000000 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v25 : ℝ := (2 : ℝ)*(Real.exp (-qv.2))
  have h25 : Bounds v25 (31/16 : ℝ) (19692307693/10000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v26 : ℝ := v8-v25
  have h26 : Bounds v26 (-20000000001/10000000000 : ℝ) (-19526367187/10000000000 : ℝ) := by
    exact (h8.sub h25).weaken (by norm_num) (by norm_num)
  let v27 : ℝ := v26+(2 : ℝ)
  have h27 : Bounds v27 (-1/10000000000 : ℝ) (473632813/10000000000 : ℝ) := by
    exact (h26.add (Bounds.refl (2 : ℝ))).weaken (by norm_num) (by norm_num)
  have hve2 : Bounds (vertexEntropy (Real.exp (-qv.2))) (-1/10000000000 : ℝ) (473632813/10000000000 : ℝ) := by
    convert h27 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v8,v25,v26,v27] <;> ring
  exact hve2

theorem coverS1Near1_hg2_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (criticalObservable (Real.exp (-qv.2))) (31/32 : ℝ) (4997449497/5000000000 : ℝ) := by
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have he2 := coverS1Near1_he2_bounds hq
  have he2p : Bounds (entropy (Real.exp (-qv.2))) 0 (161132813/10000000000 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he2.2⟩
  let v28 : ℝ := criticalOmega*(entropy (Real.exp (-qv.2)))
  have h28 : Bounds v28 (0 : ℝ) (148745147/10000000000 : ℝ) := by
    exact criticalOmega_checked_bounds.mul_corners he2p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v29 : ℝ := (Real.exp (-qv.2))+v28
  have h29 : Bounds v29 (31/32 : ℝ) (4997449497/5000000000 : ℝ) := by
    exact (hz.add h28).weaken (by norm_num) (by norm_num)
  have hg2 : Bounds (criticalObservable (Real.exp (-qv.2))) (31/32 : ℝ) (4997449497/5000000000 : ℝ) := by
    convert h29 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v28,v29] <;> ring
  exact hg2

theorem coverS1Near1_hf0_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 0 (logBoxEdges qv) coverS1Vertex0) (3803333333/5000000000 : ℝ) (155274359/200000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  let v30 : ℝ := (Real.exp (-qv.1.1))+(Real.exp (-qv.1.2))
  have h30 : Bounds v30 (63/32 : ℝ) (2 : ℝ) := by
    exact (hx.add hy).weaken (by norm_num) (by norm_num)
  let v31 : ℝ := v30+(Real.exp (-qv.2))
  have h31 : Bounds v31 (47/16 : ℝ) (29846153847/10000000000 : ℝ) := by
    exact (h30.add hz).weaken (by norm_num) (by norm_num)
  let v32 : ℝ := v31*(1/3 : ℝ)
  have h32 : Bounds v32 (4895833333/5000000000 : ℝ) (9948717949/10000000000 : ℝ) := by
    exact h31.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v33 : ℝ := v32-(7872292148643627/36028797018963968 : ℝ)
  have h33 : Bounds v33 (3803333333/5000000000 : ℝ) (155274359/200000000 : ℝ) := by
    exact (h32.sub (Bounds.refl (7872292148643627/36028797018963968 : ℝ))).weaken (by norm_num) (by norm_num)
  have hf0 : Bounds (certificateFeature 0 (logBoxEdges qv) coverS1Vertex0) (3803333333/5000000000 : ℝ) (155274359/200000000 : ℝ) := by
    convert h33 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v30,v31,v32,v33] <;> ring
  exact hf0

theorem coverS1Near1_hf1_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 1 (logBoxEdges qv) coverS1Vertex0) (2323739267/2500000000 : ℝ) (9753980179/10000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  let v34 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.2))
  have h34 : Bounds v34 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v35 : ℝ := v34*(Real.exp (-qv.2))
  have h35 : Bounds v35 (9387130737/10000000000 : ℝ) (9846153847/10000000000 : ℝ) := by
    exact h34.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v36 : ℝ := v35-criticalTriangle
  have h36 : Bounds v36 (2323739267/2500000000 : ℝ) (9753980179/10000000000 : ℝ) := by
    exact (h35.sub criticalTriangle_sharp_bounds).weaken (by norm_num) (by norm_num)
  have hf1 : Bounds (certificateFeature 1 (logBoxEdges qv) coverS1Vertex0) (2323739267/2500000000 : ℝ) (9753980179/10000000000 : ℝ) := by
    convert h36 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v34,v35,v36] <;> ring
  exact hf1

theorem coverS1Near1_hf2_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 2 (logBoxEdges qv) coverS1Vertex0) (-4610000001/10000000000 : ℝ) (-890424479/2000000000 : ℝ) := by
  have he0 := coverS1Near1_he0_bounds hq
  have he0p : Bounds (entropy (Real.exp (-qv.1.1))) 0 (1/64 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he0.2⟩
  have he1 := coverS1Near1_he1_bounds hq
  have he1p : Bounds (entropy (Real.exp (-qv.1.2))) 0 (1/64 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he1.2⟩
  have he2 := coverS1Near1_he2_bounds hq
  have he2p : Bounds (entropy (Real.exp (-qv.2))) 0 (161132813/10000000000 : ℝ) := ⟨entropy_nonneg (le_of_lt (Real.exp_pos _)),he2.2⟩
  let v37 : ℝ := (entropy (Real.exp (-qv.1.1)))+(entropy (Real.exp (-qv.1.2)))
  have h37 : Bounds v37 (0 : ℝ) (1/32 : ℝ) := by
    exact (he0p.add he1p).weaken (by norm_num) (by norm_num)
  let v38 : ℝ := v37+(entropy (Real.exp (-qv.2)))
  have h38 : Bounds v38 (0 : ℝ) (473632813/10000000000 : ℝ) := by
    exact (h37.add he2p).weaken (by norm_num) (by norm_num)
  let v39 : ℝ := v38*(1/3 : ℝ)
  have h39 : Bounds v39 (0 : ℝ) (31575521/2000000000 : ℝ) := by
    exact h38.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v40 : ℝ := v39-(8304637712871195/18014398509481984 : ℝ)
  have h40 : Bounds v40 (-4610000001/10000000000 : ℝ) (-890424479/2000000000 : ℝ) := by
    exact (h39.sub (Bounds.refl (8304637712871195/18014398509481984 : ℝ))).weaken (by norm_num) (by norm_num)
  have hf2 : Bounds (certificateFeature 2 (logBoxEdges qv) coverS1Vertex0) (-4610000001/10000000000 : ℝ) (-890424479/2000000000 : ℝ) := by
    convert h40 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v37,v38,v39,v40] <;> ring
  exact hf2

theorem coverS1Near1_hf3_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 3 (logBoxEdges qv) coverS1Vertex0) (333158287511/10000000000 : ℝ) (17204740687/500000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hmu := coverS1Near1_hmu_bounds hq
  let v41 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h41 : Bounds v41 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v42 : ℝ := v41*(Real.exp (-qv.2))
  have h42 : Bounds v42 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h41.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v43 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v42
  have h43 : Bounds v43 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hlx.add h42).weaken (by norm_num) (by norm_num)
  let v44 : ℝ := (1 : ℝ)*v43
  have h44 : Bounds v44 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v45 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h45 : Bounds v45 (67369429667/2000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v46 : ℝ := v45*(Real.exp (-qv.1.1))
  have h46 : Bounds v46 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h45.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v47 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v46
  have h47 : Bounds v47 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hly.add h46).weaken (by norm_num) (by norm_num)
  let v48 : ℝ := (1 : ℝ)*v47
  have h48 : Bounds v48 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v49 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h49 : Bounds v49 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v50 : ℝ := v49*(Real.exp (-qv.1.2))
  have h50 : Bounds v50 (336932039249/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact h49.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v51 : ℝ := (Real.log (Real.exp (-qv.2)))+v50
  have h51 : Bounds v51 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (hlz.add h50).weaken (by norm_num) (by norm_num)
  let v52 : ℝ := (1 : ℝ)*v51
  have h52 : Bounds v52 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (Bounds.refl (1 : ℝ)).mul_corners h51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v53 : ℝ := v44+v48
  have h53 : Bounds v53 (165713830821/2500000000 : ℝ) (342363752529/5000000000 : ℝ) := by
    exact (h44.add h48).weaken (by norm_num) (by norm_num)
  let v54 : ℝ := v53+v52
  have h54 : Bounds v54 (999474862533/10000000000 : ℝ) (51614222061/500000000 : ℝ) := by
    exact (h53.add h52).weaken (by norm_num) (by norm_num)
  let v55 : ℝ := v54*(1/3 : ℝ)
  have h55 : Bounds v55 (333158287511/10000000000 : ℝ) (17204740687/500000000 : ℝ) := by
    exact h54.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf3 : Bounds (certificateFeature 3 (logBoxEdges qv) coverS1Vertex0) (333158287511/10000000000 : ℝ) (17204740687/500000000 : ℝ) := by
    convert h55 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55] <;> ring
  exact hf3

theorem coverS1Near1_hf4_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 4 (logBoxEdges qv) coverS1Vertex0) (326199462501/10000000000 : ℝ) (171156235239/5000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hmu := coverS1Near1_hmu_bounds hq
  let v56 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h56 : Bounds v56 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v57 : ℝ := v56*(Real.exp (-qv.2))
  have h57 : Bounds v57 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h56.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v58 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v57
  have h58 : Bounds v58 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hlx.add h57).weaken (by norm_num) (by norm_num)
  let v59 : ℝ := (Real.exp (-qv.1.1))*v58
  have h59 : Bounds v59 (81562276107/2500000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hx.mul_corners h58 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v60 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h60 : Bounds v60 (67369429667/2000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v61 : ℝ := v60*(Real.exp (-qv.1.1))
  have h61 : Bounds v61 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h60.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v62 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v61
  have h62 : Bounds v62 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hly.add h61).weaken (by norm_num) (by norm_num)
  let v63 : ℝ := (Real.exp (-qv.1.2))*v62
  have h63 : Bounds v63 (81562276107/2500000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hy.mul_corners h62 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v64 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h64 : Bounds v64 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v65 : ℝ := v64*(Real.exp (-qv.1.2))
  have h65 : Bounds v65 (336932039249/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact h64.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v66 : ℝ := (Real.log (Real.exp (-qv.2)))+v65
  have h66 : Bounds v66 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (hlz.add h65).weaken (by norm_num) (by norm_num)
  let v67 : ℝ := (Real.exp (-qv.2))*v66
  have h67 : Bounds v67 (326100178647/10000000000 : ℝ) (2737679251/80000000 : ℝ) := by
    exact hz.mul_corners h66 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v68 : ℝ := v59+v63
  have h68 : Bounds v68 (81562276107/1250000000 : ℝ) (342363752529/5000000000 : ℝ) := by
    exact (h59.add h63).weaken (by norm_num) (by norm_num)
  let v69 : ℝ := v68+v67
  have h69 : Bounds v69 (978598387503/10000000000 : ℝ) (1026937411433/10000000000 : ℝ) := by
    exact (h68.add h67).weaken (by norm_num) (by norm_num)
  let v70 : ℝ := v69*(1/3 : ℝ)
  have h70 : Bounds v70 (326199462501/10000000000 : ℝ) (171156235239/5000000000 : ℝ) := by
    exact h69.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf4 : Bounds (certificateFeature 4 (logBoxEdges qv) coverS1Vertex0) (326199462501/10000000000 : ℝ) (171156235239/5000000000 : ℝ) := by
    convert h70 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70] <;> ring
  exact hf4

theorem coverS1Near1_hf5_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 5 (logBoxEdges qv) coverS1Vertex0) (319404157463/10000000000 : ℝ) (34055754789/1000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hmu := coverS1Near1_hmu_bounds hq
  let v71 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h71 : Bounds v71 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v72 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h72 : Bounds v72 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v73 : ℝ := v72*(Real.exp (-qv.2))
  have h73 : Bounds v73 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h72.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v74 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v73
  have h74 : Bounds v74 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hlx.add h73).weaken (by norm_num) (by norm_num)
  let v75 : ℝ := v71*v74
  have h75 : Bounds v75 (321151462163/10000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h71.mul_corners h74 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v76 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h76 : Bounds v76 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v77 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h77 : Bounds v77 (67369429667/2000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v78 : ℝ := v77*(Real.exp (-qv.1.1))
  have h78 : Bounds v78 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h77.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v79 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v78
  have h79 : Bounds v79 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hly.add h78).weaken (by norm_num) (by norm_num)
  let v80 : ℝ := v76*v79
  have h80 : Bounds v80 (321151462163/10000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h76.mul_corners h79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v81 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h81 : Bounds v81 (961/1024 : ℝ) (9694674557/10000000000 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v82 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h82 : Bounds v82 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v83 : ℝ := v82*(Real.exp (-qv.1.2))
  have h83 : Bounds v83 (336932039249/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact h82.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v84 : ℝ := (Real.log (Real.exp (-qv.2)))+v83
  have h84 : Bounds v84 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (hlz.add h83).weaken (by norm_num) (by norm_num)
  let v85 : ℝ := v81*v84
  have h85 : Bounds v85 (9872173377/312500000 : ℝ) (84236284653/2500000000 : ℝ) := by
    exact h81.mul_corners h84 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v86 : ℝ := v75+v80
  have h86 : Bounds v86 (321151462163/5000000000 : ℝ) (342363752529/5000000000 : ℝ) := by
    exact (h75.add h80).weaken (by norm_num) (by norm_num)
  let v87 : ℝ := v86+v85
  have h87 : Bounds v87 (95821247239/1000000000 : ℝ) (102167264367/1000000000 : ℝ) := by
    exact (h86.add h85).weaken (by norm_num) (by norm_num)
  let v88 : ℝ := v87*(1/3 : ℝ)
  have h88 : Bounds v88 (319404157463/10000000000 : ℝ) (34055754789/1000000000 : ℝ) := by
    exact h87.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf5 : Bounds (certificateFeature 5 (logBoxEdges qv) coverS1Vertex0) (319404157463/10000000000 : ℝ) (34055754789/1000000000 : ℝ) := by
    convert h88 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88] <;> ring
  exact hf5

theorem coverS1Near1_hf6_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 6 (logBoxEdges qv) coverS1Vertex0) (312768105259/10000000000 : ℝ) (338829624107/10000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hmu := coverS1Near1_hmu_bounds hq
  let v89 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h89 : Bounds v89 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v90 : ℝ := v89*(Real.exp (-qv.1.1))
  have h90 : Bounds v90 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h89.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v91 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h91 : Bounds v91 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v92 : ℝ := v91*(Real.exp (-qv.2))
  have h92 : Bounds v92 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h91.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v93 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v92
  have h93 : Bounds v93 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hlx.add h92).weaken (by norm_num) (by norm_num)
  let v94 : ℝ := v90*v93
  have h94 : Bounds v94 (316133470549/10000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h90.mul_corners h93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v95 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h95 : Bounds v95 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v96 : ℝ := v95*(Real.exp (-qv.1.2))
  have h96 : Bounds v96 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h95.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v97 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h97 : Bounds v97 (67369429667/2000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v98 : ℝ := v97*(Real.exp (-qv.1.1))
  have h98 : Bounds v98 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h97.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v99 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v98
  have h99 : Bounds v99 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hly.add h98).weaken (by norm_num) (by norm_num)
  let v100 : ℝ := v96*v99
  have h100 : Bounds v100 (316133470549/10000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h96.mul_corners h99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v101 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h101 : Bounds v101 (961/1024 : ℝ) (9694674557/10000000000 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v102 : ℝ := v101*(Real.exp (-qv.2))
  have h102 : Bounds v102 (9091491699/10000000000 : ℝ) (4772762859/5000000000 : ℝ) := by
    exact h101.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v103 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h103 : Bounds v103 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v104 : ℝ := v103*(Real.exp (-qv.1.2))
  have h104 : Bounds v104 (336932039249/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact h103.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v105 : ℝ := (Real.log (Real.exp (-qv.2)))+v104
  have h105 : Bounds v105 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (hlz.add h104).weaken (by norm_num) (by norm_num)
  let v106 : ℝ := v102*v105
  have h106 : Bounds v106 (7650934367/250000000 : ℝ) (331761367261/10000000000 : ℝ) := by
    exact h102.mul_corners h105 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v107 : ℝ := v94+v100
  have h107 : Bounds v107 (316133470549/5000000000 : ℝ) (342363752529/5000000000 : ℝ) := by
    exact (h94.add h100).weaken (by norm_num) (by norm_num)
  let v108 : ℝ := v107+v106
  have h108 : Bounds v108 (469152157889/5000000000 : ℝ) (1016488872319/10000000000 : ℝ) := by
    exact (h107.add h106).weaken (by norm_num) (by norm_num)
  let v109 : ℝ := v108*(1/3 : ℝ)
  have h109 : Bounds v109 (312768105259/10000000000 : ℝ) (338829624107/10000000000 : ℝ) := by
    exact h108.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf6 : Bounds (certificateFeature 6 (logBoxEdges qv) coverS1Vertex0) (312768105259/10000000000 : ℝ) (338829624107/10000000000 : ℝ) := by
    convert h109 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109] <;> ring
  exact hf6

theorem coverS1Near1_hf7_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 7 (logBoxEdges qv) coverS1Vertex0) (-3565487809/5000000000 : ℝ) (-212304803/1250000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hmu := coverS1Near1_hmu_bounds hq
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/64 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/64 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-76923077/2500000000 : ℝ) (-151367187/10000000000 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v110 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.2))
  have h110 : Bounds v110 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v111 : ℝ := v110*(Real.exp (-qv.2))
  have h111 : Bounds v111 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h110.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v112 : ℝ := (Real.log (Real.exp (-qv.1.1)))+v111
  have h112 : Bounds v112 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hlx.add h111).weaken (by norm_num) (by norm_num)
  let v113 : ℝ := v6*v112
  have h113 : Bounds v113 (-2674716817/5000000000 : ℝ) (0 : ℝ) := by
    exact h6.mul_corners h112 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v114 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.2))
  have h114 : Bounds v114 (67369429667/2000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact hmu.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v115 : ℝ := v114*(Real.exp (-qv.1.1))
  have h115 : Bounds v115 (165791955821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact h114.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v116 : ℝ := (Real.log (Real.exp (-qv.1.2)))+v115
  have h116 : Bounds v116 (165713830821/5000000000 : ℝ) (342363752529/10000000000 : ℝ) := by
    exact (hly.add h115).weaken (by norm_num) (by norm_num)
  let v117 : ℝ := v7*v116
  have h117 : Bounds v117 (-2674716817/5000000000 : ℝ) (0 : ℝ) := by
    exact h7.mul_corners h116 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v118 : ℝ := (relaxationMultiplier coverS1Vertex0)*(Real.exp (-qv.1.1))
  have h118 : Bounds v118 (342280166857/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact hmu.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v119 : ℝ := v118*(Real.exp (-qv.1.2))
  have h119 : Bounds v119 (336932039249/10000000000 : ℝ) (173856593081/5000000000 : ℝ) := by
    exact h118.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v120 : ℝ := (Real.log (Real.exp (-qv.2)))+v119
  have h120 : Bounds v120 (336619539249/10000000000 : ℝ) (173778468081/5000000000 : ℝ) := by
    exact (hlz.add h119).weaken (by norm_num) (by norm_num)
  let v121 : ℝ := v8*v120
  have h121 : Bounds v121 (-2138811917/2000000000 : ℝ) (-2547657637/5000000000 : ℝ) := by
    exact h8.mul_corners h120 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v122 : ℝ := v113+v117
  have h122 : Bounds v122 (-2674716817/2500000000 : ℝ) (0 : ℝ) := by
    exact (h113.add h117).weaken (by norm_num) (by norm_num)
  let v123 : ℝ := v122+v121
  have h123 : Bounds v123 (-21392926853/10000000000 : ℝ) (-2547657637/5000000000 : ℝ) := by
    exact (h122.add h121).weaken (by norm_num) (by norm_num)
  let v124 : ℝ := v123*(1/3 : ℝ)
  have h124 : Bounds v124 (-3565487809/5000000000 : ℝ) (-212304803/1250000000 : ℝ) := by
    exact h123.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf7 : Bounds (certificateFeature 7 (logBoxEdges qv) coverS1Vertex0) (-3565487809/5000000000 : ℝ) (-212304803/1250000000 : ℝ) := by
    convert h124 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v7,v8,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124] <;> ring
  exact hf7

theorem coverS1Near1_hf8_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 8 (logBoxEdges qv) coverS1Vertex0) (-24929294877/10000000000 : ℝ) (-23614569091/10000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hk := coverS1Near1_hk_bounds hq
  have hve0 := coverS1Near1_hve0_bounds hq
  have hve1 := coverS1Near1_hve1_bounds hq
  have hve2 := coverS1Near1_hve2_bounds hq
  let v125 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h125 : Bounds v125 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v126 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h126 : Bounds v126 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v127 : ℝ := v125-v126
  have h127 : Bounds v127 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h125.sub h126).weaken (by norm_num) (by norm_num)
  let v128 : ℝ := (Real.exp (-qv.1.1))*v127
  have h128 : Bounds v128 (-5001250001/2000000000 : ℝ) (-11843934631/5000000000 : ℝ) := by
    exact hx.mul_corners h127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v129 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h129 : Bounds v129 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v130 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h130 : Bounds v130 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v131 : ℝ := v129-v130
  have h131 : Bounds v131 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h129.sub h130).weaken (by norm_num) (by norm_num)
  let v132 : ℝ := (Real.exp (-qv.1.2))*v131
  have h132 : Bounds v132 (-5001250001/2000000000 : ℝ) (-11843934631/5000000000 : ℝ) := by
    exact hy.mul_corners h131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v133 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h133 : Bounds v133 (-1/32 : ℝ) (1/16 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v134 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h134 : Bounds v134 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v135 : ℝ := v133-v134
  have h135 : Bounds v135 (-6290625001/2500000000 : ℝ) (-969/400 : ℝ) := by
    exact (h133.sub h134).weaken (by norm_num) (by norm_num)
  let v136 : ℝ := (Real.exp (-qv.2))*v135
  have h136 : Bounds v136 (-1238769231/500000000 : ℝ) (-30039/12800 : ℝ) := by
    exact hz.mul_corners h135 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v137 : ℝ := v128+v132
  have h137 : Bounds v137 (-5001250001/1000000000 : ℝ) (-11843934631/2500000000 : ℝ) := by
    exact (h128.add h132).weaken (by norm_num) (by norm_num)
  let v138 : ℝ := v137+v136
  have h138 : Bounds v138 (-7478788463/1000000000 : ℝ) (-35421853637/5000000000 : ℝ) := by
    exact (h137.add h136).weaken (by norm_num) (by norm_num)
  let v139 : ℝ := v138*(1/3 : ℝ)
  have h139 : Bounds v139 (-24929294877/10000000000 : ℝ) (-23614569091/10000000000 : ℝ) := by
    exact h138.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf8 : Bounds (certificateFeature 8 (logBoxEdges qv) coverS1Vertex0) (-24929294877/10000000000 : ℝ) (-23614569091/10000000000 : ℝ) := by
    convert h139 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139] <;> ring
  exact hf8

theorem coverS1Near1_hf9_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 9 (logBoxEdges qv) coverS1Vertex0) (-12338571517/5000000000 : ℝ) (-11321825279/5000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hk := coverS1Near1_hk_bounds hq
  have hve0 := coverS1Near1_hve0_bounds hq
  have hve1 := coverS1Near1_hve1_bounds hq
  have hve2 := coverS1Near1_hve2_bounds hq
  let v140 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h140 : Bounds v140 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v141 : ℝ := v140*(Real.exp (-qv.1.1))
  have h141 : Bounds v141 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h140.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v142 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h142 : Bounds v142 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v143 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h143 : Bounds v143 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v144 : ℝ := v142-v143
  have h144 : Bounds v144 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h142.sub h143).weaken (by norm_num) (by norm_num)
  let v145 : ℝ := v141*v144
  have h145 : Bounds v145 (-5001250001/2000000000 : ℝ) (-22953406517/10000000000 : ℝ) := by
    exact h141.mul_corners h144 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v146 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h146 : Bounds v146 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v147 : ℝ := v146*(Real.exp (-qv.1.2))
  have h147 : Bounds v147 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h146.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v148 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h148 : Bounds v148 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v149 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h149 : Bounds v149 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v150 : ℝ := v148-v149
  have h150 : Bounds v150 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h148.sub h149).weaken (by norm_num) (by norm_num)
  let v151 : ℝ := v147*v150
  have h151 : Bounds v151 (-5001250001/2000000000 : ℝ) (-22953406517/10000000000 : ℝ) := by
    exact h147.mul_corners h150 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v152 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h152 : Bounds v152 (961/1024 : ℝ) (9694674557/10000000000 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v153 : ℝ := v152*(Real.exp (-qv.2))
  have h153 : Bounds v153 (9091491699/10000000000 : ℝ) (4772762859/5000000000 : ℝ) := by
    exact h152.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v154 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h154 : Bounds v154 (-1/32 : ℝ) (1/16 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v155 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h155 : Bounds v155 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v156 : ℝ := v154-v155
  have h156 : Bounds v156 (-6290625001/2500000000 : ℝ) (-969/400 : ℝ) := by
    exact (h154.sub h155).weaken (by norm_num) (by norm_num)
  let v157 : ℝ := v153*v156
  have h157 : Bounds v157 (-6004732273/2500000000 : ℝ) (-275301733/125000000 : ℝ) := by
    exact h153.mul_corners h156 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v158 : ℝ := v145+v151
  have h158 : Bounds v158 (-5001250001/1000000000 : ℝ) (-22953406517/5000000000 : ℝ) := by
    exact (h145.add h151).weaken (by norm_num) (by norm_num)
  let v159 : ℝ := v158+v157
  have h159 : Bounds v159 (-37015714551/5000000000 : ℝ) (-33965475837/5000000000 : ℝ) := by
    exact (h158.add h157).weaken (by norm_num) (by norm_num)
  let v160 : ℝ := v159*(1/3 : ℝ)
  have h160 : Bounds v160 (-12338571517/5000000000 : ℝ) (-11321825279/5000000000 : ℝ) := by
    exact h159.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf9 : Bounds (certificateFeature 9 (logBoxEdges qv) coverS1Vertex0) (-12338571517/5000000000 : ℝ) (-11321825279/5000000000 : ℝ) := by
    convert h160 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160] <;> ring
  exact hf9

theorem coverS1Near1_hf10_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 10 (logBoxEdges qv) coverS1Vertex0) (-306924613/125000000 : ℝ) (-22175134461/10000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hk := coverS1Near1_hk_bounds hq
  have hve0 := coverS1Near1_hve0_bounds hq
  have hve1 := coverS1Near1_hve1_bounds hq
  have hve2 := coverS1Near1_hve2_bounds hq
  let v161 : ℝ := (Real.exp (-qv.1.1))*(Real.exp (-qv.1.1))
  have h161 : Bounds v161 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hx.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v162 : ℝ := v161*(Real.exp (-qv.1.1))
  have h162 : Bounds v162 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h161.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v163 : ℝ := v162*(Real.exp (-qv.1.1))
  have h163 : Bounds v163 (2347374111/2500000000 : ℝ) (1 : ℝ) := by
    exact h162.mul_corners hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v164 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h164 : Bounds v164 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v165 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h165 : Bounds v165 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v166 : ℝ := v164-v165
  have h166 : Bounds v166 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h164.sub h165).weaken (by norm_num) (by norm_num)
  let v167 : ℝ := v163*v166
  have h167 : Bounds v167 (-5001250001/2000000000 : ℝ) (-11297379769/5000000000 : ℝ) := by
    exact h163.mul_corners h166 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v168 : ℝ := (Real.exp (-qv.1.2))*(Real.exp (-qv.1.2))
  have h168 : Bounds v168 (4844970703/5000000000 : ℝ) (1 : ℝ) := by
    exact hy.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v169 : ℝ := v168*(Real.exp (-qv.1.2))
  have h169 : Bounds v169 (9538536071/10000000000 : ℝ) (1 : ℝ) := by
    exact h168.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v170 : ℝ := v169*(Real.exp (-qv.1.2))
  have h170 : Bounds v170 (2347374111/2500000000 : ℝ) (1 : ℝ) := by
    exact h169.mul_corners hy (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v171 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h171 : Bounds v171 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v172 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h172 : Bounds v172 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v173 : ℝ := v171-v172
  have h173 : Bounds v173 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h171.sub h172).weaken (by norm_num) (by norm_num)
  let v174 : ℝ := v170*v173
  have h174 : Bounds v174 (-5001250001/2000000000 : ℝ) (-11297379769/5000000000 : ℝ) := by
    exact h170.mul_corners h173 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v175 : ℝ := (Real.exp (-qv.2))*(Real.exp (-qv.2))
  have h175 : Bounds v175 (961/1024 : ℝ) (9694674557/10000000000 : ℝ) := by
    exact hz.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v176 : ℝ := v175*(Real.exp (-qv.2))
  have h176 : Bounds v176 (9091491699/10000000000 : ℝ) (4772762859/5000000000 : ℝ) := by
    exact h175.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v177 : ℝ := v176*(Real.exp (-qv.2))
  have h177 : Bounds v177 (8807382583/10000000000 : ℝ) (9398671477/10000000000 : ℝ) := by
    exact h176.mul_corners hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v178 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h178 : Bounds v178 (-1/32 : ℝ) (1/16 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v179 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h179 : Bounds v179 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v180 : ℝ := v178-v179
  have h180 : Bounds v180 (-6290625001/2500000000 : ℝ) (-969/400 : ℝ) := by
    exact (h178.sub h179).weaken (by norm_num) (by norm_num)
  let v181 : ℝ := v177*v180
  have h181 : Bounds v181 (-5912351777/2500000000 : ℝ) (-21335884307/10000000000 : ℝ) := by
    exact h177.mul_corners h180 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v182 : ℝ := v167+v174
  have h182 : Bounds v182 (-5001250001/1000000000 : ℝ) (-11297379769/2500000000 : ℝ) := by
    exact (h167.add h174).weaken (by norm_num) (by norm_num)
  let v183 : ℝ := v182+v181
  have h183 : Bounds v183 (-36830953559/5000000000 : ℝ) (-66525403383/10000000000 : ℝ) := by
    exact (h182.add h181).weaken (by norm_num) (by norm_num)
  let v184 : ℝ := v183*(1/3 : ℝ)
  have h184 : Bounds v184 (-306924613/125000000 : ℝ) (-22175134461/10000000000 : ℝ) := by
    exact h183.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf10 : Bounds (certificateFeature 10 (logBoxEdges qv) coverS1Vertex0) (-306924613/125000000 : ℝ) (-22175134461/10000000000 : ℝ) := by
    convert h184 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184] <;> ring
  exact hf10

theorem coverS1Near1_hf11_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateFeature 11 (logBoxEdges qv) coverS1Vertex0) (122229003/10000000000 : ℝ) (103711739/2000000000 : ℝ) := by
  have hxq : qv.1.1 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 0
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hx : Bounds (Real.exp (-qv.1.1)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hxq using 1 <;> norm_num
  have hlx : Bounds (Real.log (Real.exp (-qv.1.1))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hxq using 1 <;> norm_num
  have hyq : qv.1.2 ∈ Set.Icc (0 : ℝ) (1/64 : ℝ) := by
    have h := hq 1
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hy : Bounds (Real.exp (-qv.1.2)) (63/64 : ℝ) (1 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (0 : ℝ)) hyq using 1 <;> norm_num
  have hly : Bounds (Real.log (Real.exp (-qv.1.2))) (-1/64 : ℝ) (0 : ℝ) := by
    convert log_exp_neg_bounds hyq using 1 <;> norm_num
  have hzq : qv.2 ∈ Set.Icc (1/64 : ℝ) (1/32 : ℝ) := by
    have h := hq 2
    simp only [coverS1Near1Box,LogBox.region,edgeCoordinate,Matrix.cons_val] at h
    norm_num at h ⊢
    exact h
  have hz : Bounds (Real.exp (-qv.2)) (31/32 : ℝ) (64/65 : ℝ) := by
    convert exp_neg_linear_bounds (by norm_num : (0:ℝ) ≤ (1/64 : ℝ)) hzq using 1 <;> norm_num
  have hlz : Bounds (Real.log (Real.exp (-qv.2))) (-1/32 : ℝ) (-1/64 : ℝ) := by
    convert log_exp_neg_bounds hzq using 1 <;> norm_num
  have hk := coverS1Near1_hk_bounds hq
  let v6 : ℝ := (Real.exp (-qv.1.1))*(Real.log (Real.exp (-qv.1.1)))
  have h6 : Bounds v6 (-1/64 : ℝ) (0 : ℝ) := by
    exact hx.mul_corners hlx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v7 : ℝ := (Real.exp (-qv.1.2))*(Real.log (Real.exp (-qv.1.2)))
  have h7 : Bounds v7 (-1/64 : ℝ) (0 : ℝ) := by
    exact hy.mul_corners hly (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v8 : ℝ := (Real.exp (-qv.2))*(Real.log (Real.exp (-qv.2)))
  have h8 : Bounds v8 (-76923077/2500000000 : ℝ) (-151367187/10000000000 : ℝ) := by
    exact hz.mul_corners hlz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hve0 := coverS1Near1_hve0_bounds hq
  have hve1 := coverS1Near1_hve1_bounds hq
  have hve2 := coverS1Near1_hve2_bounds hq
  let v185 : ℝ := (vertexEntropy (Real.exp (-qv.1.2)))+(vertexEntropy (Real.exp (-qv.2)))
  have h185 : Bounds v185 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve1.add hve2).weaken (by norm_num) (by norm_num)
  let v186 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h186 : Bounds v186 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v187 : ℝ := v185-v186
  have h187 : Bounds v187 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h185.sub h186).weaken (by norm_num) (by norm_num)
  let v188 : ℝ := v6*v187
  have h188 : Bounds v188 (0 : ℝ) (390722657/10000000000 : ℝ) := by
    exact h6.mul_corners h187 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v189 : ℝ := (vertexEntropy (Real.exp (-qv.2)))+(vertexEntropy (Real.exp (-qv.1.1)))
  have h189 : Bounds v189 (-156250001/10000000000 : ℝ) (786132813/10000000000 : ℝ) := by
    exact (hve2.add hve0).weaken (by norm_num) (by norm_num)
  let v190 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h190 : Bounds v190 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v191 : ℝ := v189-v190
  have h191 : Bounds v191 (-5001250001/2000000000 : ℝ) (-24063867187/10000000000 : ℝ) := by
    exact (h189.sub h190).weaken (by norm_num) (by norm_num)
  let v192 : ℝ := v7*v191
  have h192 : Bounds v192 (0 : ℝ) (390722657/10000000000 : ℝ) := by
    exact h7.mul_corners h191 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v193 : ℝ := (vertexEntropy (Real.exp (-qv.1.1)))+(vertexEntropy (Real.exp (-qv.1.2)))
  have h193 : Bounds v193 (-1/32 : ℝ) (1/16 : ℝ) := by
    exact (hve0.add hve1).weaken (by norm_num) (by norm_num)
  let v194 : ℝ := (2 : ℝ)*(relaxationVertexMean coverS1Vertex0)
  have h194 : Bounds v194 (497/200 : ℝ) (6212500001/2500000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v195 : ℝ := v193-v194
  have h195 : Bounds v195 (-6290625001/2500000000 : ℝ) (-969/400 : ℝ) := by
    exact (h193.sub h194).weaken (by norm_num) (by norm_num)
  let v196 : ℝ := v8*v195
  have h196 : Bounds v196 (36668701/1000000000 : ℝ) (774230771/10000000000 : ℝ) := by
    exact h8.mul_corners h195 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v197 : ℝ := v188+v192
  have h197 : Bounds v197 (0 : ℝ) (390722657/5000000000 : ℝ) := by
    exact (h188.add h192).weaken (by norm_num) (by norm_num)
  let v198 : ℝ := v197+v196
  have h198 : Bounds v198 (36668701/1000000000 : ℝ) (311135217/2000000000 : ℝ) := by
    exact (h197.add h196).weaken (by norm_num) (by norm_num)
  let v199 : ℝ := v198*(1/3 : ℝ)
  have h199 : Bounds v199 (122229003/10000000000 : ℝ) (103711739/2000000000 : ℝ) := by
    exact h198.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf11 : Bounds (certificateFeature 11 (logBoxEdges qv) coverS1Vertex0) (122229003/10000000000 : ℝ) (103711739/2000000000 : ℝ) := by
    convert h199 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v6,v7,v8,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199] <;> ring
  exact hf11

theorem coverS1Near1_hH_bounds {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    Bounds (certificateHoeffding (logBoxEdges qv) coverS1Vertex0) (-6642785969/10000000000 : ℝ) (-4836381113/10000000000 : ℝ) := by
  have hg0 := coverS1Near1_hg0_bounds hq
  have hg1 := coverS1Near1_hg1_bounds hq
  have hg2 := coverS1Near1_hg2_bounds hq
  let v200 : ℝ := (criticalObservable (Real.exp (-qv.1.1)))*(criticalObservable (Real.exp (-qv.1.1)))
  have h200 : Bounds v200 (4844970703/5000000000 : ℝ) (643159743/625000000 : ℝ) := by
    exact hg0.mul_corners hg0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v201 : ℝ := (criticalObservable (Real.exp (-qv.1.2)))*(criticalObservable (Real.exp (-qv.1.2)))
  have h201 : Bounds v201 (4844970703/5000000000 : ℝ) (643159743/625000000 : ℝ) := by
    exact hg1.mul_corners hg1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v202 : ℝ := (criticalObservable (Real.exp (-qv.2)))*(criticalObservable (Real.exp (-qv.2)))
  have h202 : Bounds v202 (961/1024 : ℝ) (9989800591/10000000000 : ℝ) := by
    exact hg2.mul_corners hg2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v203 : ℝ := v200+v201
  have h203 : Bounds v203 (4844970703/2500000000 : ℝ) (643159743/312500000 : ℝ) := by
    exact (h200.add h201).weaken (by norm_num) (by norm_num)
  let v204 : ℝ := v203+v202
  have h204 : Bounds v204 (28764648437/10000000000 : ℝ) (30570912367/10000000000 : ℝ) := by
    exact (h203.add h202).weaken (by norm_num) (by norm_num)
  let v205 : ℝ := v204*(1/3 : ℝ)
  have h205 : Bounds v205 (1917643229/2000000000 : ℝ) (10190304123/10000000000 : ℝ) := by
    exact h204.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v206 : ℝ := (criticalObservable (Real.exp (-qv.1.1)))*(criticalObservable (Real.exp (-qv.1.2)))
  have h206 : Bounds v206 (4844970703/5000000000 : ℝ) (643159743/625000000 : ℝ) := by
    exact hg0.mul_corners hg1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v207 : ℝ := (criticalObservable (Real.exp (-qv.1.2)))*(criticalObservable (Real.exp (-qv.2)))
  have h207 : Bounds v207 (2384033203/2500000000 : ℝ) (10139063137/10000000000 : ℝ) := by
    exact hg1.mul_corners hg2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v208 : ℝ := (criticalObservable (Real.exp (-qv.2)))*(criticalObservable (Real.exp (-qv.1.1)))
  have h208 : Bounds v208 (2384033203/2500000000 : ℝ) (10139063137/10000000000 : ℝ) := by
    exact hg2.mul_corners hg0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v209 : ℝ := v206+v207
  have h209 : Bounds v209 (9613037109/5000000000 : ℝ) (817184761/400000000 : ℝ) := by
    exact (h206.add h207).weaken (by norm_num) (by norm_num)
  let v210 : ℝ := v209+v208
  have h210 : Bounds v210 (2876220703/1000000000 : ℝ) (15284341081/5000000000 : ℝ) := by
    exact (h209.add h208).weaken (by norm_num) (by norm_num)
  let v211 : ℝ := v210*(1/3 : ℝ)
  have h211 : Bounds v211 (9587402343/10000000000 : ℝ) (10189560721/10000000000 : ℝ) := by
    exact h210.mul_corners (Bounds.refl (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v212 : ℝ := (2 : ℝ)*v211
  have h212 : Bounds v212 (9587402343/5000000000 : ℝ) (10189560721/5000000000 : ℝ) := by
    exact (Bounds.refl (2 : ℝ)).mul_corners h211 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v213 : ℝ := v205-v212
  have h213 : Bounds v213 (-10790905297/10000000000 : ℝ) (-8984500563/10000000000 : ℝ) := by
    exact (h205.sub h212).weaken (by norm_num) (by norm_num)
  let v214 : ℝ := criticalOmega*(8304637712871195/18014398509481984 : ℝ)
  have h214 : Bounds v214 (851117903/2000000000 : ℝ) (531948701/1250000000 : ℝ) := by
    exact criticalOmega_checked_bounds.mul_corners (Bounds.refl (8304637712871195/18014398509481984 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v215 : ℝ := (7872292148643627/36028797018963968 : ℝ)+v214
  have h215 : Bounds v215 (3220294757/5000000000 : ℝ) (805073701/1250000000 : ℝ) := by
    exact ((Bounds.refl (7872292148643627/36028797018963968 : ℝ)).add h214).weaken (by norm_num) (by norm_num)
  let v216 : ℝ := v215*v215
  have h216 : Bounds v216 (129628729/312500000 : ℝ) (82962389/200000000 : ℝ) := by
    exact h215.mul_corners h215 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v217 : ℝ := v213+v216
  have h217 : Bounds v217 (-6642785969/10000000000 : ℝ) (-4836381113/10000000000 : ℝ) := by
    exact (h213.add h216).weaken (by norm_num) (by norm_num)
  have hH : Bounds (certificateHoeffding (logBoxEdges qv) coverS1Vertex0) (-6642785969/10000000000 : ℝ) (-4836381113/10000000000 : ℝ) := by
    convert h217 using 1 <;>
      simp only [certificateFeature,cyclicAverage,coverEdgeResidual,coverVertexResidual,edgeTest,vertexTest,coverCycle,logBoxEdges,coverS1Vertex0,relaxationMultiplier,relaxationVertexMean,entropy,vertexEntropy,criticalObservable,certificateHoeffding,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217] <;> ring
  exact hH

/-- Actual certificate positivity throughout this entire rational box. -/
theorem coverS1Near1_positive {qv : EdgeTriple} (hq : qv ∈ coverS1Near1Box.region) :
    (1/2 : ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by
  have hf0 := coverS1Near1_hf0_bounds hq
  have hf1 := coverS1Near1_hf1_bounds hq
  have hf2 := coverS1Near1_hf2_bounds hq
  have hf3 := coverS1Near1_hf3_bounds hq
  have hf4 := coverS1Near1_hf4_bounds hq
  have hf5 := coverS1Near1_hf5_bounds hq
  have hf6 := coverS1Near1_hf6_bounds hq
  have hf7 := coverS1Near1_hf7_bounds hq
  have hf8 := coverS1Near1_hf8_bounds hq
  have hf9 := coverS1Near1_hf9_bounds hq
  have hf10 := coverS1Near1_hf10_bounds hq
  have hf11 := coverS1Near1_hf11_bounds hq
  have hH := coverS1Near1_hH_bounds hq
  let v218 : ℝ := (8639019645839429/9007199254740992 : ℝ)*(certificateFeature 0 (logBoxEdges qv) coverS1Vertex0)
  have h218 : Bounds v218 (3647867717/5000000000 : ℝ) (7446367067/10000000000 : ℝ) := by
    exact (Bounds.refl (8639019645839429/9007199254740992 : ℝ)).mul_corners hf0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v219 : ℝ := (-2657272677596523/562949953421312 : ℝ)*(certificateFeature 1 (logBoxEdges qv) coverS1Vertex0)
  have h219 : Bounds v219 (-11510341581/2500000000 : ℝ) (-4387465583/1000000000 : ℝ) := by
    exact (Bounds.refl (-2657272677596523/562949953421312 : ℝ)).mul_corners hf1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v220 : ℝ := (140737488299033/140737488355328 : ℝ)*(certificateFeature 2 (logBoxEdges qv) coverS1Vertex0)
  have h220 : Bounds v220 (-461/1000 : ℝ) (-4452122393/10000000000 : ℝ) := by
    exact (Bounds.refl (140737488299033/140737488355328 : ℝ)).mul_corners hf2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v221 : ℝ := (-7541973450629039/36893488147419103232 : ℝ)*(certificateFeature 3 (logBoxEdges qv) coverS1Vertex0)
  have h221 : Bounds v221 (-70341789/10000000000 : ℝ) (-34053041/5000000000 : ℝ) := by
    exact (Bounds.refl (-7541973450629039/36893488147419103232 : ℝ)).mul_corners hf3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v222 : ℝ := (-8604084221028639/72057594037927936 : ℝ)*(certificateFeature 4 (logBoxEdges qv) coverS1Vertex0)
  have h222 : Bounds v222 (-40874044787/10000000000 : ℝ) (-38950060513/10000000000 : ℝ) := by
    exact (Bounds.refl (-8604084221028639/72057594037927936 : ℝ)).mul_corners hf4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v223 : ℝ := (1019507261509151/1125899906842624 : ℝ)*(certificateFeature 5 (logBoxEdges qv) coverS1Vertex0)
  have h223 : Bounds v223 (289221853479/10000000000 : ℝ) (61675268099/2000000000 : ℝ) := by
    exact (Bounds.refl (1019507261509151/1125899906842624 : ℝ)).mul_corners hf5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v224 : ℝ := (-7199522257880297/9007199254740992 : ℝ)*(certificateFeature 6 (logBoxEdges qv) coverS1Vertex0)
  have h224 : Bounds v224 (-54165814509/2000000000 : ℝ) (-49999580817/2000000000 : ℝ) := by
    exact (Bounds.refl (-7199522257880297/9007199254740992 : ℝ)).mul_corners hf6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v225 : ℝ := (8774057038934945/72057594037927936 : ℝ)*(certificateFeature 7 (logBoxEdges qv) coverS1Vertex0)
  have h225 : Bounds v225 (-434149847/5000000000 : ℝ) (-51702377/2500000000 : ℝ) := by
    exact (Bounds.refl (8774057038934945/72057594037927936 : ℝ)).mul_corners hf7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v226 : ℝ := (-2521529215217977/18014398509481984 : ℝ)*(certificateFeature 8 (logBoxEdges qv) coverS1Vertex0)
  have h226 : Bounds v226 (3305401833/10000000000 : ℝ) (3489427933/10000000000 : ℝ) := by
    exact (Bounds.refl (-2521529215217977/18014398509481984 : ℝ)).mul_corners hf8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v227 : ℝ := (7097966112403971/18014398509481984 : ℝ)*(certificateFeature 9 (logBoxEdges qv) coverS1Vertex0)
  have h227 : Bounds v227 (-486159793/500000000 : ℝ) (-4460983369/5000000000 : ℝ) := by
    exact (Bounds.refl (7097966112403971/18014398509481984 : ℝ)).mul_corners hf9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v228 : ℝ := (-6881924343606227/9007199254740992 : ℝ)*(certificateFeature 10 (logBoxEdges qv) coverS1Vertex0)
  have h228 : Bounds v228 (8471423433/5000000000 : ℝ) (3752077699/2000000000 : ℝ) := by
    exact (Bounds.refl (-6881924343606227/9007199254740992 : ℝ)).mul_corners hf10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v229 : ℝ := (3354424007516313/4503599627370496 : ℝ)*(certificateFeature 11 (logBoxEdges qv) coverS1Vertex0)
  have h229 : Bounds v229 (45520021/5000000000 : ℝ) (386238983/10000000000 : ℝ) := by
    exact (Bounds.refl (3354424007516313/4503599627370496 : ℝ)).mul_corners hf11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v230 : ℝ := v229+(0 : ℝ)
  have h230 : Bounds v230 (45520021/5000000000 : ℝ) (386238983/10000000000 : ℝ) := by
    exact (h229.add (Bounds.refl (0 : ℝ))).weaken (by norm_num) (by norm_num)
  let v231 : ℝ := v228+v230
  have h231 : Bounds v231 (4258471727/2500000000 : ℝ) (9573313739/5000000000 : ℝ) := by
    exact (h228.add h230).weaken (by norm_num) (by norm_num)
  let v232 : ℝ := v227+v231
  have h232 : Bounds v232 (913836381/1250000000 : ℝ) (511233037/500000000 : ℝ) := by
    exact (h227.add h231).weaken (by norm_num) (by norm_num)
  let v233 : ℝ := v226+v232
  have h233 : Bounds v233 (10616092881/10000000000 : ℝ) (13714088673/10000000000 : ℝ) := by
    exact (h226.add h232).weaken (by norm_num) (by norm_num)
  let v234 : ℝ := v225+v233
  have h234 : Bounds v234 (9747793187/10000000000 : ℝ) (2701455833/2000000000 : ℝ) := by
    exact (h225.add h233).weaken (by norm_num) (by norm_num)
  let v235 : ℝ := v224+v234
  have h235 : Bounds v235 (-130540639679/5000000000 : ℝ) (-5912265623/250000000 : ℝ) := by
    exact (h224.add h234).weaken (by norm_num) (by norm_num)
  let v236 : ℝ := v223+v235
  have h236 : Bounds v236 (28140574121/10000000000 : ℝ) (2875428623/400000000 : ℝ) := by
    exact (h223.add h235).weaken (by norm_num) (by norm_num)
  let v237 : ℝ := v222+v236
  have h237 : Bounds v237 (-6366735333/5000000000 : ℝ) (16467827531/5000000000 : ℝ) := by
    exact (h222.add h236).weaken (by norm_num) (by norm_num)
  let v238 : ℝ := v221+v237
  have h238 : Bounds v238 (-2560762491/2000000000 : ℝ) (1643377449/500000000 : ℝ) := by
    exact (h221.add h237).weaken (by norm_num) (by norm_num)
  let v239 : ℝ := v220+v238
  have h239 : Bounds v239 (-3482762491/2000000000 : ℝ) (28415426587/10000000000 : ℝ) := by
    exact (h220.add h238).weaken (by norm_num) (by norm_num)
  let v240 : ℝ := v219+v239
  have h240 : Bounds v240 (-63455178779/10000000000 : ℝ) (-15459229243/10000000000 : ℝ) := by
    exact (h219.add h239).weaken (by norm_num) (by norm_num)
  let v241 : ℝ := v218+v240
  have h241 : Bounds v241 (-11231888669/2000000000 : ℝ) (-250401943/312500000 : ℝ) := by
    exact (h218.add h240).weaken (by norm_num) (by norm_num)
  let v242 : ℝ := (0 : ℝ)-v241
  have h242 : Bounds v242 (250401943/312500000 : ℝ) (11231888669/2000000000 : ℝ) := by
    exact ((Bounds.refl (0 : ℝ)).sub h241).weaken (by norm_num) (by norm_num)
  let v243 : ℝ := (1080863910568919/1125899906842624 : ℝ)*(certificateHoeffding (logBoxEdges qv) coverS1Vertex0)
  have h243 : Bounds v243 (-6377074531/10000000000 : ℝ) (-1160731467/2500000000 : ℝ) := by
    exact (Bounds.refl (1080863910568919/1125899906842624 : ℝ)).mul_corners hH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let v244 : ℝ := v242-v243
  have h244 : Bounds v244 (3163947011/2500000000 : ℝ) (15634129469/2500000000 : ℝ) := by
    exact (h242.sub h243).weaken (by norm_num) (by norm_num)
  have heq : v244 = logCertificate coverS1Theta coverS1Lam coverS1Vertex0 qv := by
    dsimp only [v218,v219,v220,v221,v222,v223,v224,v225,v226,v227,v228,v229,v230,v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244]
    rw [logCertificate,coverCertificate_fin12_expansion]
    simp only [coverS1Theta,coverS1Lam,Matrix.cons_val]
    ring
  rw [heq] at h244
  exact lt_of_lt_of_le (by norm_num) h244.1

end SparseLowerTail.Section05
