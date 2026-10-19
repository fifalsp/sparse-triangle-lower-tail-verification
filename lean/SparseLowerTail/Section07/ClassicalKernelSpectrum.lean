import SparseLowerTail.Section07.DegreeBounds
import Mathlib.MeasureTheory.Function.L2Space

/-! Explicit classical spectral input for positive Hilbert--Schmidt kernels.

Mathlib 4.24's `Analysis.InnerProductSpace.Spectrum` provides finite-dimensional
spectral theory and lists compact self-adjoint spectral theory as a TODO. The
proposition below is the standard compact positive self-adjoint spectral theorem
on L²([0,1]), with its Hilbert--Schmidt kernel/trace formulations. It is an
explicit theorem parameter, never a global axiom.

The input is completely independent of graphons: it applies to every symmetric
square-integrable real kernel whose quadratic form is nonnegative. It supplies
measurable orthonormal eigenfunctions, genuine integral eigen-equations,
square-summable eigenvalues, L² kernel convergence, a.e. L² sections with
rowwise Parseval for every finite spectral tail, positive residual forms and
the standard cubic trace identity. It does NOT supply trace-class membership,
a bound on the sum of eigenvalues, diagonal bounds, graphon degree estimates,
rank-one approximation bounds, or any rigidity assertion from this paper.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SparseLowerTail.Section07
open Section04

/-- A finite spectral kernel sum. -/
def spectralPartial (ev : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ i∈Finset.range N, ev i*e i p.1*e i p.2

/-- Positive semidefiniteness of an actual L² kernel, stated using its integral. -/
def PositiveKernelForm (K : ℝ × ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, MemLp f 2 unitMeasure →
    0≤(∫ p, K p*(f p.1*f p.2) ∂squareMeasure)

/-- Standard spectral data for a positive Hilbert--Schmidt integral kernel.
Zero eigenvalues pad a finite-rank decomposition, with orthonormal vectors
chosen in the null space. No trace-class assertion is included. -/
structure KernelSpectralExpansion (K : ℝ × ℝ → ℝ) where
  eigenvalue : ℕ → ℝ
  eigenfunction : ℕ → ℝ → ℝ
  eigenvalue_nonneg : ∀ i, 0≤eigenvalue i
  eigenvalue_antitone : Antitone eigenvalue
  eigenfunction_measurable : ∀ i, Measurable (eigenfunction i)
  eigenfunction_memLp : ∀ i, MemLp (eigenfunction i) 2 unitMeasure
  orthonormal_integral : ∀ i j,
    (∫ x, eigenfunction i x*eigenfunction j x ∂unitMeasure)=if i=j then 1 else 0
  eigen_equation : ∀ i, ∀ᵐ x ∂unitMeasure,
    (∫ y, K (x,y)*eigenfunction i y ∂unitMeasure)=eigenvalue i*eigenfunction i x
  square_summable : Summable (fun i => eigenvalue i^2)
  square_sum : (∑' i, eigenvalue i^2)=∫ p, K p^2 ∂squareMeasure
  kernel_convergence : Tendsto
    (fun N => ∫ p, (K p-spectralPartial eigenvalue eigenfunction N p)^2 ∂squareMeasure)
    atTop (𝓝 0)
  row_memLp : ∀ᵐ x ∂unitMeasure, MemLp (fun y => K (x,y)) 2 unitMeasure
  row_tail_parseval : ∀ N, ∀ᵐ x ∂unitMeasure,
    Summable (fun i => eigenvalue (i+N)^2*(eigenfunction (i+N) x)^2) ∧
    (∫ y, (K (x,y)-spectralPartial eigenvalue eigenfunction N (x,y))^2 ∂unitMeasure)=
      ∑' i, eigenvalue (i+N)^2*(eigenfunction (i+N) x)^2
  residual_positive : ∀ N, PositiveKernelForm
    (fun p => K p-spectralPartial eigenvalue eigenfunction N p)
  cube_summable : Summable (fun i => eigenvalue i^3)
  cube_integrable : Integrable
    (fun p : ℝ × (ℝ × ℝ) => K (p.1,p.2.1)*K (p.2.1,p.2.2)*K (p.1,p.2.2)) cubeMeasure
  cube_sum : (∑' i, eigenvalue i^3)=
    ∫ p : ℝ × (ℝ × ℝ), K (p.1,p.2.1)*K (p.2.1,p.2.2)*K (p.1,p.2.2) ∂cubeMeasure

/-- Classical external input: the compact positive self-adjoint spectral theorem
and its Hilbert--Schmidt integral-kernel realization on the atomless unit interval. -/
def PositiveKernelSpectralTheorem : Prop :=
  ∀ K : ℝ × ℝ → ℝ, MemLp K 2 squareMeasure →
    (∀ᵐ p ∂squareMeasure, K p.swap=K p) → PositiveKernelForm K →
    Nonempty (KernelSpectralExpansion K)

/-- All hypotheses needed to apply the classical theorem to the paper's actual
centered kernel are proved internally. -/
theorem centeredKernel_spectral_expansion (hSpectral : PositiveKernelSpectralTheorem)
    (hSampling : UniformSampling) {r γ : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hγ : 0≤γ)
    {U : Graphon} (hU : IsMinimizer r U)
    (hpen : ∀ W : Graphon, cost U+γ*triangle U≤cost W+γ*triangle W) :
    Nonempty (KernelSpectralExpansion (centeredKernel U)) := by
  have hb := centeredKernel_bounded U
  obtain ⟨C,_,hC⟩ := hb.bound
  refine hSpectral (centeredKernel U)
    (MemLp.of_bound hb.measurable.aestronglyMeasurable C hC) (centeredKernel_symmetric U) ?_
  intro f hf
  exact penalized_centeredKernel_positive hSampling hr hγ hU hpen
    (MemLp.integrable (by norm_num : (1:ENNReal)≤2) hf)

end SparseLowerTail.Section07
