import SparseLowerTail.Section03.FiniteTriangleAttainment
import SparseLowerTail.Section03.NearMinimizers

/-! Balanced finite colorings for graphon recovery vectors, for every vertex count. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SparseLowerTail.Section03

/-- Split n vertices into complete K-color batches and fewer than K remaining vertices. -/
def recoveryVertexEquiv (K n : ℕ) :
    Fin n ≃ ((Fin (n/K)×Fin K) ⊕ Fin (n%K)) := Fintype.equivOfCardEq (by
  simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_prod]
  simpa only [Nat.mul_comm] using (Nat.div_add_mod n K).symm)

/-- Every complete batch contains each color once; leftover vertices receive color zero. -/
def balancedVertexColor (K : ℕ) (hK : 0<K) (n : ℕ) (i : Fin n) : Fin K :=
  match recoveryVertexEquiv K n i with
  | Sum.inl ij => ij.2
  | Sum.inr _ => ⟨0,hK⟩

/-- Exact color sum, including all leftover vertices. -/
theorem sum_balancedVertexColor (K : ℕ) (hK : 0<K) (n : ℕ) (f : Fin K → ℝ) :
    (∑ i, f (balancedVertexColor K hK n i))=
      ((n/K:ℕ):ℝ)*(∑ a, f a)+((n%K:ℕ):ℝ)*f ⟨0,hK⟩ := by
  calc
    _ = ∑ t : (Fin (n/K)×Fin K) ⊕ Fin (n%K), f (match t with
      | Sum.inl ij => ij.2 | Sum.inr _ => ⟨0,hK⟩) :=
        Fintype.sum_equiv (recoveryVertexEquiv K n) _ _ (fun _ => rfl)
    _ = _ := by simp [Fintype.sum_sum_type,Fintype.sum_prod_type]

/-- Empirical mass of a color in the actual n-vertex coloring. -/
def balancedColorMass (K : ℕ) (hK : 0<K) (n : ℕ) (a : Fin K) : ℝ :=
  (∑ i : Fin n, if balancedVertexColor K hK n i=a then (1:ℝ) else 0)/(n:ℝ)

theorem balancedColorMass_formula (K : ℕ) (hK : 0<K) (n : ℕ) (a : Fin K) :
    balancedColorMass K hK n a=((n/K:ℕ):ℝ)/(n:ℝ)+
      (if a=⟨0,hK⟩ then ((n%K:ℕ):ℝ)/(n:ℝ) else 0) := by
  classical
  unfold balancedColorMass
  rw [sum_balancedVertexColor K hK n (fun b => if b=a then (1:ℝ) else 0)]
  by_cases ha : a=⟨0,hK⟩ <;> simp [ha,Ne.symm,add_div]

/-- The normalized leftover count vanishes. -/
theorem remainder_fraction_tendsto (K : ℕ) (hK : 0<K) :
    Tendsto (fun n : ℕ => ((n%K:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hhi : Tendsto (fun n : ℕ => (K:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.mod_lt n hK).le) (Nat.cast_nonneg n)) hhi

/-- Every color has limiting frequency 1/K, without restricting n to multiples of K. -/
theorem balancedColorMass_tendsto (K : ℕ) (hK : 0<K) (a : Fin K) :
    Tendsto (fun n => balancedColorMass K hK n a) atTop (𝓝 (1/(K:ℝ))) := by
  have hK0 : (K:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hdiv : ∀ n : ℕ, 0<n → ((n/K:ℕ):ℝ)/(n:ℝ)=
      1/(K:ℝ)-(((n%K:ℕ):ℝ)/(n:ℝ))/(K:ℝ) := by
    intro n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have he : (K:ℝ)*((n/K:ℕ):ℝ)+((n%K:ℕ):ℝ)=(n:ℝ) := by
      exact_mod_cast Nat.div_add_mod n K
    field_simp [hK0,hn0]
    nlinarith
  have hbatch : Tendsto (fun n : ℕ => ((n/K:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 (1/(K:ℝ))) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1/(K:ℝ)) atTop (𝓝 (1/(K:ℝ)))).sub ((remainder_fraction_tendsto K hK).div_const (K:ℝ))
    simp only [zero_div,sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (hdiv n hn).symm
  simp_rw [balancedColorMass_formula]
  by_cases ha : a=⟨0,hK⟩
  · simp only [ha,ite_true]
    simpa only [add_zero] using hbatch.add (remainder_fraction_tendsto K hK)
  · simpa only [ha,ite_false,add_zero] using hbatch

end SparseLowerTail.Section03
