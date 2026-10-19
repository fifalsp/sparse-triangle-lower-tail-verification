import SparseLowerTail.Section05.RelaxedLaw

/-! Exact finite-dimensional certificate functions, stable anchors `eq:features`,
`def:certificate`, `s5:Psi`. Cyclic averaging gives the manuscript's symmetric
averages because each base residual is symmetric in its other two coordinates. -/
noncomputable section
namespace SparseLowerTail.Section05
open Section04

/-- The cyclic coordinate permutation (A,B,C) ↦ (B,C,A). -/
def coverCycle (u : EdgeTriple) : EdgeTriple := ((u.1.2,u.2),u.1.1)

/-- Average over the three choices of distinguished edge. -/
def cyclicAverage (f : EdgeTriple → ℝ) (u : EdgeTriple) : ℝ :=
  (f u+f (coverCycle u)+f (coverCycle (coverCycle u)))/3

def coverEdgeResidual (j : Fin 5) (π : ℝ × ℝ) (u : EdgeTriple) : ℝ :=
  edgeTest j u.1.1*(Real.log u.1.1+relaxationMultiplier π*u.1.2*u.2)

def coverVertexResidual (j : Fin 4) (π : ℝ × ℝ) (u : EdgeTriple) : ℝ :=
  vertexTest j u.1.1*(vertexEntropy u.1.2+vertexEntropy u.2-2*relaxationVertexMean π)

/-- The twelve actual features E₀,…,E₁₁. The Euler features use yz rather
than xyz/x, with the equality on the positive domain proved separately. -/
def certificateFeature (i : Fin 12) (u : EdgeTriple) (π : ℝ × ℝ) : ℝ :=
  ![cyclicAverage (fun v => v.1.1) u-π.1,
    u.1.1*u.1.2*u.2-criticalTriangle,
    cyclicAverage (fun v => entropy v.1.1) u-π.2,
    cyclicAverage (coverEdgeResidual 0 π) u,
    cyclicAverage (coverEdgeResidual 1 π) u,
    cyclicAverage (coverEdgeResidual 2 π) u,
    cyclicAverage (coverEdgeResidual 3 π) u,
    cyclicAverage (coverEdgeResidual 4 π) u,
    cyclicAverage (coverVertexResidual 0 π) u,
    cyclicAverage (coverVertexResidual 1 π) u,
    cyclicAverage (coverVertexResidual 2 π) u,
    cyclicAverage (coverVertexResidual 3 π) u] i

/-- The symmetrized Hoeffding integrand H*. -/
def certificateHoeffding (u : EdgeTriple) (π : ℝ × ℝ) : ℝ :=
  cyclicAverage (fun v => (criticalObservable v.1.1)^2) u-
    2*cyclicAverage (fun v => criticalObservable v.1.1*criticalObservable v.1.2) u+
    (π.1+criticalOmega*π.2)^2

/-- The certificate Ψ with twelve coefficients and nonnegative multiplier λ. -/
def coverCertificate (θ : Fin 12 → ℝ) (lam : ℝ) (u : EdgeTriple) (π : ℝ × ℝ) : ℝ :=
  -(∑ i, θ i*certificateFeature i u π)-lam*certificateHoeffding u π

theorem coverEdgeResidual_product_div {u : EdgeTriple} (hu : u.1.1 ≠ 0)
    (j : Fin 5) (π : ℝ × ℝ) :
    coverEdgeResidual j π u = edgeTest j u.1.1*(Real.log u.1.1+
      relaxationMultiplier π*(u.1.1*u.1.2*u.2/u.1.1)) := by
  unfold coverEdgeResidual
  field_simp

end SparseLowerTail.Section05
