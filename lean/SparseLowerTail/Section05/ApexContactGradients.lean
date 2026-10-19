import SparseLowerTail.Section05.ApexTangency

/-! Symmetry reduces six contact derivatives to the three distinct equations
in the four-by-four tangency system. All identities concern the actual Ψ. -/
noncomputable section
namespace SparseLowerTail.Section05
open Numerics Certificate

def apexSwap12 (q : ApexVector) : ApexVector := ![q 1,q 0,q 2]
def apexSwap23 (q : ApexVector) : ApexVector := ![q 0,q 2,q 1]
def apexSwap12Index : Fin 3 → Fin 3 := ![1,0,2]
def apexSwap23Index : Fin 3 → Fin 3 := ![0,2,1]

theorem apexPhi_swap12 (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) :
    apexPhi θ lam (apexSwap12 q)=apexPhi θ lam q := by
  simpa only [apexPhi,logCertificate,apexSwap12,Matrix.cons_val,logBoxEdges,edgeSwap12_apply]
    using coverCertificate_swap12 θ lam
      ((Real.exp (-q 0),Real.exp (-q 1)),Real.exp (-q 2)) criticalPoint

theorem apexPhi_swap23 (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) :
    apexPhi θ lam (apexSwap23 q)=apexPhi θ lam q := by
  simpa only [apexPhi,logCertificate,apexSwap23,Matrix.cons_val,logBoxEdges,edgeSwap23_apply]
    using coverCertificate_swap23 θ lam
      ((Real.exp (-q 0),Real.exp (-q 1)),Real.exp (-q 2)) criticalPoint

theorem apexGradient_swap12 (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i : Fin 3) :
    apexGradient θ lam (apexSwap12 q) i=apexGradient θ lam q (apexSwap12Index i) := by
  have h := apexPhi_coordinate_deriv θ lam (apexSwap12 q) i
  have hfun : (fun t => apexPhi θ lam (familySegment (apexSwap12 q) (apexCoordinate i) t))=
      (fun t => apexPhi θ lam (familySegment q (apexCoordinate (apexSwap12Index i)) t)) := by
    funext t
    have he : familySegment (apexSwap12 q) (apexCoordinate i) t=
        apexSwap12 (familySegment q (apexCoordinate (apexSwap12Index i)) t) := by
      funext j
      fin_cases i <;> fin_cases j <;> simp [familySegment,apexSwap12,apexCoordinate,apexSwap12Index]
    rw [he,apexPhi_swap12]
  rw [hfun] at h
  exact h.unique (apexPhi_coordinate_deriv θ lam q (apexSwap12Index i))

theorem apexGradient_swap23 (θ : Fin 12 → ℝ) (lam : ℝ) (q : ApexVector) (i : Fin 3) :
    apexGradient θ lam (apexSwap23 q) i=apexGradient θ lam q (apexSwap23Index i) := by
  have h := apexPhi_coordinate_deriv θ lam (apexSwap23 q) i
  have hfun : (fun t => apexPhi θ lam (familySegment (apexSwap23 q) (apexCoordinate i) t))=
      (fun t => apexPhi θ lam (familySegment q (apexCoordinate (apexSwap23Index i)) t)) := by
    funext t
    have he : familySegment (apexSwap23 q) (apexCoordinate i) t=
        apexSwap23 (familySegment q (apexCoordinate (apexSwap23Index i)) t) := by
      funext j
      fin_cases i <;> fin_cases j <;> simp [familySegment,apexSwap23,apexCoordinate,apexSwap23Index]
    rw [he,apexPhi_swap23]
  rw [hfun] at h
  exact h.unique (apexPhi_coordinate_deriv θ lam q (apexSwap23Index i))

theorem apexAAA_gradient_zero {θ : Fin 12 → ℝ} {lam : ℝ}
    (h : apexGradient θ lam apexContactAAA 0=0) :
    ∀i,apexGradient θ lam apexContactAAA i=0 := by
  have hs12 : apexSwap12 apexContactAAA=apexContactAAA := by funext i; fin_cases i <;> rfl
  have hs23 : apexSwap23 apexContactAAA=apexContactAAA := by funext i; fin_cases i <;> rfl
  have h1 := apexGradient_swap12 θ lam apexContactAAA 1
  have h2 := apexGradient_swap23 θ lam apexContactAAA 2
  rw [hs12] at h1
  rw [hs23] at h2
  change apexGradient θ lam apexContactAAA 1=apexGradient θ lam apexContactAAA 0 at h1
  change apexGradient θ lam apexContactAAA 2=apexGradient θ lam apexContactAAA 1 at h2
  intro i
  fin_cases i
  · exact h
  · exact h1.trans h
  · exact h2.trans (h1.trans h)

theorem apexABB_gradient_zero {θ : Fin 12 → ℝ} {lam : ℝ}
    (h0 : apexGradient θ lam apexContactABB 0=0)
    (h1 : apexGradient θ lam apexContactABB 1=0) :
    ∀i,apexGradient θ lam apexContactABB i=0 := by
  have hs23 : apexSwap23 apexContactABB=apexContactABB := by funext i; fin_cases i <;> rfl
  have h2 := apexGradient_swap23 θ lam apexContactABB 2
  rw [hs23] at h2
  change apexGradient θ lam apexContactABB 2=apexGradient θ lam apexContactABB 1 at h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2.trans h1

/-- The four solved equations imply both full contact jets. -/
theorem apexTangency_contacts {θ : Fin 12 → ℝ} {lam : ℝ}
    (h : apexTangencyResidual θ lam=0) :
    (apexPhi θ lam apexContactAAA=0 ∧ ∀i,apexGradient θ lam apexContactAAA i=0) ∧
    (apexPhi θ lam apexContactABB=0 ∧ ∀i,apexGradient θ lam apexContactABB i=0) := by
  have h0 : apexPhi θ lam apexContactAAA=0 := congrFun h 0
  have h1 : apexGradient θ lam apexContactAAA 0=0 := congrFun h 1
  have h2 : apexGradient θ lam apexContactABB 0=0 := congrFun h 2
  have h3 : apexGradient θ lam apexContactABB 1=0 := congrFun h 3
  exact ⟨⟨h0,apexAAA_gradient_zero h1⟩,⟨apexPhi_ABB_zero_of_AAA h0,apexABB_gradient_zero h2 h3⟩⟩

end SparseLowerTail.Section05
