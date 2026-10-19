import SparseLowerTail.Section06.InsertionTriangle
import SparseLowerTail.Section04.VertexIdentity

/-! The insertion first variation and the row-functional lower bound. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SparseLowerTail.Section06
open Section04

/-- The row functional in `s3:J`, with its multiplier explicit. -/
def rowFunctional (U : Graphon) (μ : ℝ) (v : ℝ → ℝ) : ℝ :=
  2*(∫ x, entropy (v x) ∂unitMeasure)+μ*rowQuadratic U v

def insertionPath (hSampling : UniformSampling) (U : PointwiseGraphon) (v : VertexProfile)
    (s : ℝ) : Graphon :=
  if s=0 then U.toGraphon else if hs : s ∈ Icc (0:ℝ) 1 then
    insertedGraphon hSampling U v s hs else U.toGraphon

@[simp] theorem insertionPath_zero (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) :
    insertionPath hSampling U v 0=U.toGraphon := by simp [insertionPath]

theorem insertionPath_cost (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    cost (insertionPath hSampling U v s)=
      (1-s)^2*cost U.toGraphon+2*s*(1-s)*(∫ x, entropy (v x) ∂unitMeasure)+s^2 := by
  by_cases hz : s=0
  · subst s; simp
  · simp only [insertionPath,if_neg hz,dif_pos hs]
    exact insertedGraphon_cost hSampling U v hs

theorem insertionPath_edge (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    edgeDensity (insertionPath hSampling U v s)=
      (1-s)^2*edgeDensity U.toGraphon+2*s*(1-s)*(∫ x, v x ∂unitMeasure) := by
  by_cases hz : s=0
  · subst s; simp
  · simp only [insertionPath,if_neg hz,dif_pos hs]
    exact insertedGraphon_edge hSampling U v hs

theorem insertionPath_triangle (hSampling : UniformSampling)
    (U : PointwiseGraphon) (v : VertexProfile) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    triangle (insertionPath hSampling U v s)=
      (1-s)^3*triangle U.toGraphon+3*s*(1-s)^2*rowQuadratic U.toGraphon v.toFun := by
  by_cases hz : s=0
  · subst s; simp
  · simp only [insertionPath,if_neg hz,dif_pos hs]
    exact insertedGraphon_triangle hSampling U v hs

private theorem pairPolynomial_derivative (F H : ℝ) :
    HasDerivAt (fun s : ℝ => (1-s)^2*F+2*s*(1-s)*H) (2*H-2*F) 0 := by
  have hid := hasDerivAt_id (0:ℝ)
  have hlin := (hasDerivAt_const (0:ℝ) 1).sub hid
  convert ((hlin.pow 2).mul_const F).add (((hid.const_mul 2).mul hlin).mul_const H) using 1 <;> norm_num <;> ring

private theorem trianglePolynomial_derivative (t Q : ℝ) :
    HasDerivAt (fun s : ℝ => (1-s)^3*t+3*s*(1-s)^2*Q) (3*Q-3*t) 0 := by
  have hid := hasDerivAt_id (0:ℝ)
  have hlin := (hasDerivAt_const (0:ℝ) 1).sub hid
  convert ((hlin.pow 3).mul_const t).add (((hid.const_mul 3).mul (hlin.pow 2)).mul_const Q) using 1 <;> norm_num <;> ring

/-- `lem:insertion`, lower-bound part, for an everywhere representative.
The graphon path and its three polynomial moments are constructed, not assumed. -/
theorem rowFunctional_ge_vertexMean_pointwise (hSampling : UniformSampling)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) (U : PointwiseGraphon)
    (hU : IsMinimizer r U.toGraphon) (v : VertexProfile) :
    vertexMean U.toGraphon r ≤ rowFunctional U.toGraphon (graphonMultiplier U.toGraphon r) v.toFun := by
  let W := fun s => NonnegativeKernel.ofGraphon (insertionPath hSampling U v s)
  have hF : HasDerivWithinAt (fun s => (W s).cost)
      (2*(∫ x, entropy (v x) ∂unitMeasure)-2*cost U.toGraphon) (Icc (0:ℝ) 1) 0 := by
    have hd := (pairPolynomial_derivative (cost U.toGraphon) (∫ x, entropy (v x) ∂unitMeasure)).add
      ((hasDerivAt_id (0:ℝ)).pow 2)
    have hd' : HasDerivAt (fun s : ℝ => (1-s)^2*cost U.toGraphon+
        2*s*(1-s)*(∫ x, entropy (v x) ∂unitMeasure)+s^2)
        (2*(∫ x, entropy (v x) ∂unitMeasure)-2*cost U.toGraphon) 0 := by
      simpa using hd
    exact hd'.hasDerivWithinAt.congr (fun s hs => insertionPath_cost hSampling U v hs)
      (by simp [W])
  have he : HasDerivWithinAt (fun s => (W s).edgeDensity)
      (2*(∫ x, v x ∂unitMeasure)-2*edgeDensity U.toGraphon) (Icc (0:ℝ) 1) 0 := by
    exact (pairPolynomial_derivative _ _).hasDerivWithinAt.congr
      (fun s hs => insertionPath_edge hSampling U v hs) (by simp [W])
  have ht : HasDerivWithinAt (fun s => (W s).triangle)
      (3*rowQuadratic U.toGraphon v.toFun-3*triangle U.toGraphon) (Icc (0:ℝ) 1) 0 := by
    exact (trianglePolynomial_derivative _ _).hasDerivWithinAt.congr
      (fun s hs => insertionPath_triangle hSampling U v hs) (by simp [W])
  have h := rescaling_firstVariation_right_interval hr (by norm_num : (0:ℝ)<1) hU
    (W := W) (by simp only [W,insertionPath_zero]; exact Filter.EventuallyEq.rfl) hF he ht
  rw [minimizer_triangle_eq hr hU] at h
  unfold vertexMean rowFunctional
  nlinarith

end SparseLowerTail.Section06
