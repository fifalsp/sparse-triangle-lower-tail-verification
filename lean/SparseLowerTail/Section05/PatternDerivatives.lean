import SparseLowerTail.Numerics.BoxLowerBounds

/-! Equality of actual partial derivatives at symmetric contact patterns. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section05

def coordinateUnit (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

def coordinateSwap (i j : Fin 3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k=>x (Equiv.swap i j k)

/-- Swapping coordinates transports a coordinate line at a fixed point to its partner. -/
theorem coordinateSwap_line (i j : Fin 3) (P : Fin 3 → ℝ) (t : ℝ) (hP : P i=P j) :
    coordinateSwap i j (P+t•coordinateUnit i)=P+t•coordinateUnit j := by
  by_cases hij:i=j
  · subst j
    ext k
    simp [coordinateUnit,coordinateSwap]
  · ext k
    by_cases hki:k=i
    · subst k
      simp [coordinateUnit,coordinateSwap,hij,Ne.symm hij,hP]
    · by_cases hkj:k=j
      · subst k
        simp [coordinateUnit,coordinateSwap,hP]
      · simp [coordinateUnit,coordinateSwap,Equiv.swap_apply_def,hki,hkj]

/-- A local permutation identity forces equality of the corresponding actual partials. -/
theorem partials_eq_of_coordinateSwap
    {Φ : (Fin 3 → ℝ) → ℝ} {P : Fin 3 → ℝ} {D : (Fin 3 → ℝ) →L[ℝ] ℝ}
    (hΦ : HasFDerivAt Φ D P) (i j : Fin 3) (hP : P i=P j)
    (hsym : ∀ᶠ x in 𝓝 P, Φ (coordinateSwap i j x)=Φ x) :
    D (coordinateUnit i)=D (coordinateUnit j) := by
  have hp (k:Fin 3) : HasDerivAt (fun t:ℝ=>P+t•coordinateUnit k) (coordinateUnit k) 0 := by
    simpa only [zero_add,one_smul] using
      (hasDerivAt_const (0:ℝ) P).add ((hasDerivAt_id (0:ℝ)).smul_const (coordinateUnit k))
  have hd (k:Fin 3) : HasDerivAt (fun t:ℝ=>Φ (P+t•coordinateUnit k)) (D (coordinateUnit k)) 0 := by
    simpa only [Function.comp_def] using hΦ.comp_hasDerivAt_of_eq 0 (hp k) (by simp)
  have ht : Tendsto (fun t:ℝ=>P+t•coordinateUnit i) (𝓝 0) (𝓝 P) := by
    simpa using (hp i).continuousAt.tendsto
  have he := ht.eventually hsym
  have heq : (fun t:ℝ=>Φ (P+t•coordinateUnit j)) =ᶠ[𝓝 0]
      (fun t:ℝ=>Φ (P+t•coordinateUnit i)) := by
    filter_upwards [he] with t ht
    exact (congrArg Φ (coordinateSwap_line i j P t hP)).symm.trans ht
  exact ((hd i).congr_of_eventuallyEq heq).unique (hd j)

/-- The invariant open domain in the paper supplies the required local identity. -/
theorem partials_eq_of_coordinateSwap_on_open
    {Φ : (Fin 3 → ℝ) → ℝ} {G : Set (Fin 3 → ℝ)} {P : Fin 3 → ℝ}
    {D : (Fin 3 → ℝ) →L[ℝ] ℝ} (hG : IsOpen G) (hPG : P∈G)
    (hΦ : HasFDerivAt Φ D P) (i j : Fin 3) (hP : P i=P j)
    (hsym : ∀ x∈G, Φ (coordinateSwap i j x)=Φ x) :
    D (coordinateUnit i)=D (coordinateUnit j) :=
  partials_eq_of_coordinateSwap hΦ i j hP
    (eventually_of_mem (hG.mem_nhds hPG) hsym)

/-- At (p,p,p), all three partial derivatives agree. -/
theorem partials_eq_at_AAA {Φ : (Fin 3 → ℝ) → ℝ} {G : Set (Fin 3 → ℝ)} {p : ℝ}
    {D : (Fin 3 → ℝ) →L[ℝ] ℝ} (hG : IsOpen G) (hPG : (fun _=>p)∈G)
    (hΦ : HasFDerivAt Φ D (fun _=>p))
    (h01 : ∀ x∈G, Φ (coordinateSwap 0 1 x)=Φ x)
    (h12 : ∀ x∈G, Φ (coordinateSwap 1 2 x)=Φ x) :
    D (coordinateUnit 0)=D (coordinateUnit 1) ∧ D (coordinateUnit 1)=D (coordinateUnit 2) :=
  ⟨partials_eq_of_coordinateSwap_on_open hG hPG hΦ 0 1 rfl h01,
    partials_eq_of_coordinateSwap_on_open hG hPG hΦ 1 2 rfl h12⟩

/-- At (p,p',p'), the two repeated-coordinate partials agree. -/
theorem partials_eq_at_ABB {Φ : (Fin 3 → ℝ) → ℝ} {G : Set (Fin 3 → ℝ)} {p p' : ℝ}
    {D : (Fin 3 → ℝ) →L[ℝ] ℝ} (hG : IsOpen G) (hPG : ![p,p',p']∈G)
    (hΦ : HasFDerivAt Φ D ![p,p',p'])
    (h12 : ∀ x∈G, Φ (coordinateSwap 1 2 x)=Φ x) :
    D (coordinateUnit 1)=D (coordinateUnit 2) :=
  partials_eq_of_coordinateSwap_on_open hG hPG hΦ 1 2 rfl h12

/-- The diagonal contact statement using differentiability and the actual Fréchet derivative. -/
theorem partials_at_AAA_of_differentiable {Φ : (Fin 3 → ℝ) → ℝ}
    {G : Set (Fin 3 → ℝ)} {p : ℝ} (hG : IsOpen G) (hPG : (fun _=>p)∈G)
    (hΦ : DifferentiableAt ℝ Φ (fun _=>p))
    (h01 : ∀ x∈G, Φ (coordinateSwap 0 1 x)=Φ x)
    (h12 : ∀ x∈G, Φ (coordinateSwap 1 2 x)=Φ x) :
    fderiv ℝ Φ (fun _=>p) (coordinateUnit 0)=fderiv ℝ Φ (fun _=>p) (coordinateUnit 1) ∧
    fderiv ℝ Φ (fun _=>p) (coordinateUnit 1)=fderiv ℝ Φ (fun _=>p) (coordinateUnit 2) :=
  partials_eq_at_AAA hG hPG hΦ.hasFDerivAt h01 h12

/-- The repeated-coordinate contact statement using the actual Fréchet derivative. -/
theorem partials_at_ABB_of_differentiable {Φ : (Fin 3 → ℝ) → ℝ}
    {G : Set (Fin 3 → ℝ)} {p p' : ℝ} (hG : IsOpen G) (hPG : ![p,p',p']∈G)
    (hΦ : DifferentiableAt ℝ Φ ![p,p',p'])
    (h12 : ∀ x∈G, Φ (coordinateSwap 1 2 x)=Φ x) :
    fderiv ℝ Φ ![p,p',p'] (coordinateUnit 1)=fderiv ℝ Φ ![p,p',p'] (coordinateUnit 2) :=
  partials_eq_at_ABB hG hPG hΦ.hasFDerivAt h12

end SparseLowerTail.Section05
