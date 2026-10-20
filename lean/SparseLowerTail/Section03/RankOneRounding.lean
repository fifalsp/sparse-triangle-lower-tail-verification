import SparseLowerTail.Section03.SignRounding

/-! L¹ and balance estimates for a rounded rank-one sign kernel. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section03
open Section02

/-- A scalar rank-one sign kernel changes by at most twice the sign's L¹ error. -/
theorem signedRankOneKernel_l1_le (ℓ μ : ℝ) {g s : ℝ → ℝ}
    (hg : Measurable g) (hs : Measurable s)
    (hga : ∀ x, |g x|=1) (hsa : ∀ x, |s x|=1) :
    (∫ p, |signedRankOneKernel ℓ μ g p-signedRankOneKernel ℓ μ s p| ∂squareMeasure)≤
      2*|μ| * (∫ x, |s x-g x| ∂unitMeasure) := by
  have hgint := unitBound_integrable hg (fun x => (hga x).le)
  have hsint := unitBound_integrable hs (fun x => (hsa x).le)
  have hi : Integrable (fun x => |s x-g x|) unitMeasure := by
    simpa only [Real.norm_eq_abs] using (hsint.sub hgint).norm
  have hleft : Integrable (fun p => |signedRankOneKernel ℓ μ g p-signedRankOneKernel ℓ μ s p|) squareMeasure := by
    simpa only [Real.norm_eq_abs] using
      ((signedRankOneKernel_integrable ℓ μ hg (fun x => (hga x).le)).sub
      (signedRankOneKernel_integrable ℓ μ hs (fun x => (hsa x).le))).norm
  have hright := ((hi.comp_fst unitMeasure).add (hi.comp_snd unitMeasure)).const_mul |μ|
  have hh := integral_mono hleft hright (fun p => ?_)
  · have he : (∫ p : ℝ×ℝ, |μ| * (|s p.1-g p.1|+|s p.2-g p.2|) ∂squareMeasure)=
        2*|μ| * (∫ x, |s x-g x| ∂unitMeasure) := by
      rw [integral_const_mul,integral_add (hi.comp_fst unitMeasure) (hi.comp_snd unitMeasure)]
      change |μ| * ((∫ p : ℝ×ℝ, |s p.1-g p.1| ∂unitMeasure.prod unitMeasure)+
        ∫ p : ℝ×ℝ, |s p.2-g p.2| ∂unitMeasure.prod unitMeasure)=_
      rw [integral_fun_fst (fun x => |s x-g x|),integral_fun_snd (fun x => |s x-g x|)]
      simp
      ring
    simpa only [Pi.add_apply] using hh.trans_eq he
  · have he : signedRankOneKernel ℓ μ g p-signedRankOneKernel ℓ μ s p=
        μ*((g p.1-s p.1)*g p.2+s p.1*(g p.2-s p.2)) := by dsimp [signedRankOneKernel]; ring
    rw [he,abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg μ)
    calc
      _≤|(g p.1-s p.1)*g p.2|+|s p.1*(g p.2-s p.2)| := abs_add_le _ _
      _=_ := by rw [abs_mul,abs_mul,hga,hsa,mul_one,one_mul,abs_sub_comm (g p.1),abs_sub_comm (g p.2)]
                rfl

/-- Balanced signs yield a quantitative cardinality bound for the rounded vertex partition. -/
theorem roundedVertexSet_balance {n : ℕ} (hn : 0<n) (P : VertexPartition n)
    (hmass : ∀ i, unitMeasure.real (P.fiber i)=1/(n:ℝ))
    {g : ℝ → ℝ} (hg : Measurable g) (hb : ∀ x, g x=1 ∨ g x=-1)
    (hmean : (∫ x, g x ∂unitMeasure)=0) :
    |((roundedVertexSet P g).card:ℝ)-(n:ℝ)/2|≤
      (n:ℝ)/2*(1-∫ x, (projectedVertexTest P g x)^2 ∂unitMeasure) := by
  have hgabs : ∀ x, |g x|≤1 := fun x => by rcases hb x with h|h <;> simp [h]
  have hi := (unitBound_integrable (roundedVertexTest_measurable P g)
    (fun x => (roundedVertexTest_abs P g x).le)).sub (unitBound_integrable hg hgabs)
  have hh := norm_integral_le_integral_norm (f:=fun x => roundedVertexTest P g x-g x) (μ:=unitMeasure)
  rw [integral_sub (unitBound_integrable (roundedVertexTest_measurable P g)
    (fun x => (roundedVertexTest_abs P g x).le)) (unitBound_integrable hg hgabs),hmean,sub_zero,
    roundedVertexTest_integral hn P hmass] at hh
  simp only [Real.norm_eq_abs] at hh
  have hbound := hh.trans (roundedVertexTest_l1_error hn P hmass hg hb)
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he : |((roundedVertexSet P g).card:ℝ)-(n:ℝ)/2|=
      (n:ℝ)/2*|2*(roundedVertexSet P g).card/(n:ℝ)-1| := by
    have hm : (n:ℝ)/2*(2*(roundedVertexSet P g).card/(n:ℝ)-1)=
        ((roundedVertexSet P g).card:ℝ)-(n:ℝ)/2 := by field_simp
    calc
      _=|(n:ℝ)/2*(2*(roundedVertexSet P g).card/(n:ℝ)-1)| := congrArg abs hm.symm
      _=_ := by rw [abs_mul,abs_of_pos (div_pos hn' (by norm_num))]
  rw [he]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end SparseLowerTail.Section03
