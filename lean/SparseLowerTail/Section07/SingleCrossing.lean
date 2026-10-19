import SparseLowerTail.Section07.Fold
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Elementary one-dimensional upward-crossing topology. This avoids assuming
finiteness of the zero set and is used for the penalized gap. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section07

/-- A continuous function whose derivatives at zeros are positive cannot pass
from a nonnegative value to a negative value. -/
theorem no_downward_crossing {f : ℝ → ℝ} {p q : ℝ} (hpq : p<q)
    (hc : ∀ x ∈ Icc p q, ContinuousAt f x)
    (hd : ∀ x ∈ Icc p q, f x=0 → 0<deriv f x)
    (hp : 0≤f p) (hq : f q<0) : False := by
  let S := Icc p q ∩ f ⁻¹' Ici 0
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    ((show ContinuousOn f (Icc p q) from fun x hx => (hc x hx).continuousWithinAt).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici) (fun _ hx => hx.1)
  obtain ⟨c,hcmax⟩ := hS.exists_isGreatest ⟨p,⟨⟨le_rfl,hpq.le⟩,hp⟩⟩
  have hcp : p≤c := hcmax.1.1.1
  have hcq : c<q := lt_of_le_of_ne hcmax.1.1.2 (by
    intro he
    have hh : 0≤f c := hcmax.1.2
    rw [he] at hh
    linarith)
  have hfc : f c=0 := by
    apply le_antisymm _ hcmax.1.2
    by_contra hn
    have hfcpos : 0<f c := lt_of_not_ge hn
    have hfpos : ∀ᶠ x in 𝓝[>] c, 0<f x :=
      ((hc c hcmax.1.1).tendsto.eventually (eventually_gt_nhds hfcpos)).filter_mono nhdsWithin_le_nhds
    have hlt : ∀ᶠ x in 𝓝[>] c, x<q :=
      (eventually_lt_nhds hcq).filter_mono nhdsWithin_le_nhds
    obtain ⟨x,hx,hxq,hfx⟩ := ((show ∀ᶠ x in 𝓝[>] c, c<x from self_mem_nhdsWithin).and (hlt.and hfpos)).exists
    have hxc : c<x := hx
    have hh := hcmax.2 (show x∈S from ⟨⟨hcp.trans hxc.le,hxq.le⟩,hfx.le⟩)
    linarith
  have hmax : IsLocalMaxOn f (Ici c) c := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hcq).filter_mono nhdsWithin_le_nhds] with x hx hxq
    rw [hfc]
    by_cases he : x=c
    · simp [he,hfc]
    · have hcx : c<x := lt_of_le_of_ne (show c≤x from hx) (Ne.symm he)
      by_contra hn
      have hfx : 0<f x := lt_of_not_ge hn
      have hh := hcmax.2 (show x∈S from ⟨⟨hcp.trans hcx.le,hxq.le⟩,hfx.le⟩)
      linarith
  have hcone : (1:ℝ) ∈ posTangentConeAt (Ici c) c := by
    apply one_mem_posTangentConeAt_iff_frequently.mpr
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact le_of_lt (show c<x from hx)
  have hdc := hd c hcmax.1.1 hfc
  have hdiff := (differentiableAt_of_deriv_ne_zero (ne_of_gt hdc)).hasDerivAt
  have hnon := hmax.hasFDerivWithinAt_nonpos hdiff.hasDerivWithinAt.hasFDerivWithinAt hcone
  have hn : deriv f c≤0 := by simpa using hnon
  linarith

/-- After an upward crossing the function remains strictly positive, provided
all later zeros would also be upward crossings. -/
theorem positive_after_upward_crossing {f : ℝ → ℝ} {p q : ℝ} (hpq : p<q)
    (hc : ∀ x ∈ Icc p q, ContinuousAt f x)
    (hd : ∀ x ∈ Icc p q, f x=0 → 0<deriv f x) (hp : 0≤f p) : 0<f q := by
  have hqnon : 0≤f q := by
    by_contra hn
    exact no_downward_crossing hpq hc hd hp (lt_of_not_ge hn)
  by_contra hn
  have hq : f q=0 := le_antisymm (le_of_not_gt hn) hqnon
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos (hd q ⟨hpq.le,le_rfl⟩ hq) hq
  have hsign' : ∀ᶠ x in 𝓝[<] q, f x<0 := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with x hx hxt
    rw [sign_neg (sub_neg.mpr (show x<q from hxt))] at hx
    exact sign_eq_neg_one_iff.mp hx
  obtain ⟨x,hx,hxp,hfx⟩ := ((show ∀ᶠ x in 𝓝[<] q, x<q from self_mem_nhdsWithin).and
    (((eventually_gt_nhds hpq).filter_mono nhdsWithin_le_nhds).and hsign')).exists
  have hxq : x<q := hx
  exact no_downward_crossing hxp
    (fun y hy => hc y ⟨hy.1,hy.2.trans hxq.le⟩)
    (fun y hy => hd y ⟨hy.1,hy.2.trans hxq.le⟩) hp hfx

end SparseLowerTail.Section07
