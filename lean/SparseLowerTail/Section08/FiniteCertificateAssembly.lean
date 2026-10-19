import SparseLowerTail.Section08.ContinuationAssembly
import SparseLowerTail.Section08.CertificateTail
import SparseLowerTail.Section08.FamilyParameterRange
import SparseLowerTail.Section07.SmallTailAssembly

/-! The main theorem now reduces to the critical classification and the compact
intermediate certificate. Small-target classification and the family parameter
range are proved here through their completed components, not hypotheses. -/
noncomputable section
open Set
namespace SparseLowerTail.Section08
open Section02 Section04 Section05 Section06 Section07

/-- Own-paper finite-certificate obligation. The box and parameter interval are
explicit; this is not an external theorem or a global axiom. -/
def CompactFamilyCertificate : Prop :=
  ∀ z : ℝ,0<z → branchLog z∈Icc (39/10:ℝ) (19/2) → Certificate.CompactLogCertificate z

/-- The full small-target classification, with precisely the permitted inputs. -/
theorem smallRangeClassification (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem) :
    SmallRangeClassification :=
  fun _ hr => smallTarget_classification external hSampling hSpectral hr

/-- Checked parameter inclusion and the analytic tail turn the compact family
certificate into exactly the pointwise statement used by continuation. -/
theorem middleFamilyCertificate_of_compact (hfamily : CompactFamilyCertificate) :
    MiddleFamilyCertificate := by
  intro r hr
  have hz : 0<leftBranch r := penalizedCrossing_mem_unit.1.trans_le
    (middle_branch_parameter_bounds hr).1
  have hL := middle_branch_log_range hr
  have hh := Certificate.family_certificate_of_compact_exact hz hL (hfamily _ hz hL)
  intro x hx y hy w hw
  exact ⟨(hh x hx y hy w hw).1,(hh x hx y hy w hw).2.mp⟩

/-- Latest conditional main theorem: only critical classification and the compact
family remain internal proof obligations. All other parameters are named
external/classical results. This theorem does not assert either certificate. -/
theorem mainTheorem_of_finite_certificates (external : KP26PenalizedReduction)
    (hSampling : UniformSampling) (hSpectral : PositiveKernelSpectralTheorem)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hcrit : CriticalClassification) (hfamily : CompactFamilyCertificate) : MainTheorem :=
  mainTheorem_of_remaining_inputs hSampling hdyadic hcompact hpull hcount hcrit
    (smallRangeClassification external hSampling hSpectral)
    (middleFamilyCertificate_of_compact hfamily)

end SparseLowerTail.Section08
