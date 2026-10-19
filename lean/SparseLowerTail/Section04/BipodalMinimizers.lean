import SparseLowerTail.Section04.VertexIdentity

/-! `cor:bipodalmin` for actual graphon minimizers. The only extra input is
classical inverse-transform sampling; all first-order and rigidity arguments
are proved. Relabeling equivalence is tracked separately as `lem:relabelB`. -/
noncomputable section
open Set
namespace SparseLowerTail.Section04

theorem bipodal_minimizer_classification (hSampling : UniformSampling)
    {r c a d b : ℝ} {U : Graphon} (hr : r ∈ Ioo (0 : ℝ) threshold)
    (hmin : IsMinimizer r U) (hB : IsBipodal U c a d b) :
    IsBalanced U (branchA (leftBranch r)) (branchB (leftBranch r)) ∧
      value r = balancedValue r := by
  exact bipodal_minimizer_of_vertex_identity hr hmin hB
    (minimizer_vertex_identity hSampling ⟨hr.1, hr.2.trans threshold_mem_Ioo.2⟩ hmin)

end SparseLowerTail.Section04
