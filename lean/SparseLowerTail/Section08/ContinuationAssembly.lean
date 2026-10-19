import SparseLowerTail.MainTheoremAssembly
import SparseLowerTail.Continuation
import SparseLowerTail.Section08.Boundary
import SparseLowerTail.Section08.TieExclusion
import SparseLowerTail.Section07.SmallData

/-! Actual graphon continuation and conditional main-theorem assembly.
The three remaining INTERNAL obligations are CriticalClassification,
SmallRangeClassification, and MiddleFamilyCertificate. They are propositions
passed as hypotheses, not axioms and not classical external results. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section08
open Section02 Section04 Section05 Section06 Section07

/-- Internal own-paper obligation `thm:smalltail`, with exact graphon semantics. -/
def SmallRangeClassification : Prop :=
  ∀ r∈Ioc (0:ℝ) smallTarget,BranchClassification r

/-- Internal own-paper obligation: the pointwise family certificate on precisely
the branch parameters needed by continuation. It has no minimizer conclusion. -/
def MiddleFamilyCertificate : Prop :=
  ∀ r∈Icc smallTarget threshold,
    ∀ x∈Ioc (0:ℝ) 1,∀ y∈Ioc (0:ℝ) 1,∀ w∈Ioc (0:ℝ) 1,
      0≤Certificate.psi (leftBranch r) x y w ∧
      (Certificate.psi (leftBranch r) x y w=0 →
        AllowedPattern (branchA (leftBranch r)) (branchB (leftBranch r)) x y w)

/-- Every relevant branch parameter lies in the proved coefficient-sign range;
this is deduced from monotonicity and the kernel-checked transition digits. -/
theorem leftBranch_le_one_fortieth {r : ℝ} (hr : r∈Ioc (0:ℝ) threshold) :
    0<leftBranch r ∧ leftBranch r≤1/40 := by
  have htspin : threshold<spinodalValue := by
    rw [threshold_eq_transitionTarget]
    exact transitionTarget_spec.1.2
  have hrs : r∈Ioo (0:ℝ) spinodalValue := ⟨hr.1,hr.2.trans_lt htspin⟩
  have hmono := strictMonoOn_leftBranch.monotoneOn ⟨hr.1.le,hrs.2.le⟩
    ⟨threshold_mem_Ioo.1.le,htspin.le⟩ hr.2
  have he : leftBranch threshold=transitionParameter := by
    rw [threshold_eq_transitionTarget]
    rfl
  rw [he] at hmono
  have hbound : transitionParameter<1/40 :=
    transitionParameter_digits.2.trans (by norm_num [digitZUpper])
  exact ⟨(leftBranch_mem_unit hrs).1,hmono.trans hbound.le⟩

/-- Actual branch classification gives the value identity used by the boundary lemma. -/
theorem value_eq_branchCost_of_classification {r : ℝ} (hr : r∈Ioo (0:ℝ) threshold)
    (h : BranchClassification r) : value r=branchCost (leftBranch r) := by
  have hrt : r∈Ioo (0:ℝ) transitionTarget := by
    simpa only [threshold_eq_transitionTarget] using hr
  exact (value_eq_balancedValue_of_branchClassification hr h).trans
    (balancedValue_below_transition hrt).1

/-- A boundary of an interval of classified targets is itself classified once
it lies in the middle certificate range. Boundary data and tie exclusion are
both instantiated for every actual minimizer. -/
theorem branchClassification_boundary (hdyadic : ClassicalDyadicL1Approximation)
    (hcompact : ClassicalGraphonCompactness) (hcount : ClassicalTriangleCounting)
    (hfamily : MiddleFamilyCertificate) {r : ℝ} (hrlo : smallTarget≤r)
    (hrhi : r<threshold) (habove : ∀ s,r<s → s<threshold → BranchClassification s) :
    BranchClassification r := by
  have hr0 : 0<r := smallTarget_mem_unit.1.trans_le hrlo
  have hr : r∈Ioo (0:ℝ) threshold := ⟨hr0,hrhi⟩
  apply branchClassification_of_minimizers hdyadic hcompact hcount hr
  intro U hU
  have hvalues : ∀ s∈Ioo r threshold,value s=branchCost (leftBranch s) := by
    intro s hs
    exact value_eq_branchCost_of_classification ⟨hr0.trans hs.1,hs.2⟩ (habove s hs.1 hs.2)
  obtain ⟨hF,he⟩ := boundary hr0 hrhi le_rfl hvalues hU
  have hz := leftBranch_le_one_fortieth ⟨hr0,hrhi.le⟩
  have hrspin : r<spinodalValue := by
    rw [threshold_eq_transitionTarget] at hrhi
    exact hrhi.trans transitionTarget_spec.1.2
  have ht : balancedTriangle (branchA (leftBranch r)) (branchB (leftBranch r))=r^3 := by
    rw [branch_triangle_eq_rho_cube hz.1,branchRho_leftBranch ⟨hr0.le,hrspin.le⟩]
  exact Certificate.minimizer_balanced_of_tie_certificate ⟨hr0,hrhi.trans threshold_mem_Ioo.2⟩
    hz.1 hz.2 hU ht hF he (hfamily r ⟨hrlo,hrhi.le⟩)

/-- All subcritical classifications follow by the proved graphon openness,
seed, boundary lemma and tie exclusion. The own-paper small-range and family
certificate statements remain explicit internal inputs. -/
theorem branchClassification_all_subcritical (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hcrit : CriticalClassification) (hsmall : SmallRangeClassification)
    (hfamily : MiddleFamilyCertificate) :
    ∀ r∈Ioo (0:ℝ) threshold,BranchClassification r := by
  have hall := classification_on_interval BranchClassification smallTarget threshold
    smallTarget_mem_unit.1
    (fun r hr hlo => hsmall r ⟨hr,hlo⟩)
    (by
      intro r hr hrt hg
      obtain ⟨δ,hδ,_,hh⟩ := branchClassification_open hSampling hdyadic hcompact hpull hcount ⟨hr,hrt⟩ hg
      refine ⟨δ,hδ,?_⟩
      intro s hs hsr _
      exact hh s ⟨hs,hsr.trans_lt (by linarith)⟩)
    (by
      obtain ⟨δ,hδ,hlo,hh⟩ := branchClassification_seed hSampling hdyadic hcompact hpull hcount hcrit
      exact ⟨threshold-δ,hlo,by linarith,fun r hr hrt => hh r ⟨hr,hrt⟩⟩)
    (fun r hr hrt habove => branchClassification_boundary hdyadic hcompact hcount hfamily hr hrt habove)
  exact fun r hr => hall r hr.1 hr.2

/-- Conditional final assembly with the minimal remaining internal obligations
shown separately from the permitted classical analytic inputs. This is not an
unconditional proof until the three internal propositions are discharged. -/
theorem mainTheorem_of_remaining_inputs (hSampling : UniformSampling)
    (hdyadic : ClassicalDyadicL1Approximation) (hcompact : ClassicalGraphonCompactness)
    (hpull : ClassicalPullbackApproximation) (hcount : ClassicalTriangleCounting)
    (hcrit : CriticalClassification) (hsmall : SmallRangeClassification)
    (hfamily : MiddleFamilyCertificate) : MainTheorem :=
  mainTheorem_of_classifications hcrit
    (branchClassification_all_subcritical hSampling hdyadic hcompact hpull hcount hcrit hsmall hfamily)

end SparseLowerTail.Section08
