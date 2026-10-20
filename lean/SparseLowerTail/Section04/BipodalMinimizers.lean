import SparseLowerTail.Section04.VertexIdentity
import SparseLowerTail.Section02.RelabelBalanced

/-! `cor:bipodalmin` for actual graphon minimizers. The only extra input is
classical inverse-transform sampling; all first-order and rigidity arguments
are proved. The literal relabeling conclusion also uses classical CDF transport. -/
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

/-- The manuscript's actual relabeling conclusion, together with equality of
the unrestricted and balanced values. Both branch bounds are derived. -/
theorem bipodal_minimizer_relabeling (hSampling : UniformSampling)
    (hCDF : Section02.ClassicalCDFTransport) {r c a d b : ℝ} {U : Graphon}
    (hr : r ∈ Ioo (0 : ℝ) threshold) (hmin : IsMinimizer r U)
    (hB : IsBipodal U c a d b) :
    (∃ (ha : branchA (leftBranch r) ∈ Icc (0 : ℝ) 1)
      (hb : branchB (leftBranch r) ∈ Icc (0 : ℝ) 1),
      Section02.IsBalancedRelabeling U (branchA (leftBranch r))
        (branchB (leftBranch r)) ha hb) ∧ value r = balancedValue r := by
  obtain ⟨hbal, hvalue⟩ := bipodal_minimizer_classification hSampling hr hmin hB
  have hrt : r ∈ Ioo (0 : ℝ) transitionTarget := by
    simpa only [threshold_eq_transitionTarget] using hr
  have hm := (balancedMinimizer_below_transition hrt _ _).mpr ⟨rfl, rfl⟩
  exact ⟨⟨hm.1.1, hm.1.2.1,
    Section02.IsBalanced.exists_relabel hCDF hbal hm.1.1 hm.1.2.1⟩, hvalue⟩

end SparseLowerTail.Section04
