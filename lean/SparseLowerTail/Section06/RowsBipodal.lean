import SparseLowerTail.Section06.RowRigidity
import SparseLowerTail.Section04.BipodalGraphon
import SparseLowerTail.Section02.CutDistanceIdentities

/-! The measurable row criterion for bipodality, including relabeling invariance. -/
noncomputable section
open MeasureTheory Set Filter
namespace SparseLowerTail.Section06
open Section02 Section04
attribute [local instance] Classical.propDecidable

/-- Reverse Fubini for equality of a.e. measurable kernels. -/
theorem ae_eq_of_ae_rows {f g : ℝ × ℝ → ℝ} (hf : AEMeasurable f squareMeasure)
    (hg : AEMeasurable g squareMeasure)
    (h : ∀ᵐ x ∂unitMeasure,∀ᵐ y ∂unitMeasure,f (x,y)=g (x,y)) :
    f =ᵐ[squareMeasure] g := by
  have hm : ∀ᵐ x ∂unitMeasure,∀ᵐ y ∂unitMeasure,hf.mk f (x,y)=hg.mk g (x,y) := by
    filter_upwards [h,Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with x hx hfx hgx
    filter_upwards [hx,hfx,hgx] with y hxy hfxy hgxy
    exact hfxy.symm.trans (hxy.trans hgxy)
  have he : hf.mk f =ᵐ[squareMeasure] hg.mk g :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk)).mpr hm
  exact hf.ae_eq_mk.trans (he.trans hg.ae_eq_mk.symm)

/-- A partition may be intersected with [0,1] without changing its graphon. -/
theorem isBipodal_of_blockValue {P : Set ℝ} (hP : MeasurableSet P) {U : Graphon}
    {a d b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hU : U.toFun =ᵐ[squareMeasure] bipodalBlockValue P a d b) :
    IsBipodal U (unitMeasure.real P) a d b := by
  classical
  let Q := P∩Icc (0:ℝ) 1
  have hi : ∀ᵐ x ∂unitMeasure,x∈Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have he : Q =ᵐ[unitMeasure] P := hi.mono fun x hx => by
    apply propext
    change (x∈P∩Icc (0:ℝ) 1) ↔ x∈P
    simp only [mem_inter_iff,hx,and_true]
  refine ⟨⟨measureReal_nonneg,measureReal_le_one⟩,ha,hd,hb,Q,
    hP.inter measurableSet_Icc,inter_subset_right,?_,?_⟩
  · rw [measure_congr he]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  · filter_upwards [hU,Measure.quasiMeasurePreserving_fst.ae hi,
      Measure.quasiMeasurePreserving_snd.ae hi] with p hp hx hy
    simpa only [bipodalBlockValue,Q,mem_inter_iff,hx,hy,and_true] using hp

/-- `lem:rowsbipodal`: two row types and symmetry force three block constants. -/
theorem bipodal_of_two_rows {P : Set ℝ} (hP : MeasurableSet P)
    (hp : unitMeasure P≠0) (hpc : unitMeasure Pᶜ≠0) {U : Graphon} {f g : ℝ→ℝ}
    (hrows : U.toFun =ᵐ[squareMeasure] (fun p => if p.1∈P then f p.2 else g p.2)) :
    ∃ a d b : ℝ,IsBipodal U (unitMeasure.real P) a d b := by
  classical
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hrows
  have hs : ∀ᵐ p ∂squareMeasure,
      (if p.1∈P then f p.2 else g p.2)=(if p.2∈P then f p.1 else g p.1) := by
    filter_upwards [hrows,hswap,U.symmetric] with p hx hy hs
    exact hx.symm.trans (hs.symm.trans hy)
  have hs' := Measure.ae_ae_of_ae_prod hs
  obtain ⟨x,hx,hfx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp (ae_restrict_of_ae hs')
  obtain ⟨y,hy,hfy,hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpc
    (ae_restrict_of_ae (hs'.and hfx))
  have hyn : y∉P := hy
  have hcross : f y=g x := by simpa [hx,hyn] using hxy
  let a := f x
  let d := g y
  let b := g x
  have hf : f =ᵐ[unitMeasure] (fun z => if z∈P then a else b) := by
    simpa only [hx,if_true,a,b] using hfx
  have hg : g =ᵐ[unitMeasure] (fun z => if z∈P then b else d) := by
    simpa only [hyn,if_false,hcross,b,d] using hfy
  have he : U.toFun =ᵐ[squareMeasure] bipodalBlockValue P a d b := by
    filter_upwards [hrows,Measure.quasiMeasurePreserving_snd.ae hf,
      Measure.quasiMeasurePreserving_snd.ae hg] with p hp hf hg
    rw [hp]
    dsimp only [bipodalBlockValue]
    split_ifs with hx hy <;> simp_all
  have hc : unitMeasure.real P∈Ioo (0:ℝ) 1 := by
    have hpos : 0<unitMeasure.real P := ENNReal.toReal_pos hp (measure_ne_top _ _)
    have hcpos : 0<unitMeasure.real Pᶜ := ENNReal.toReal_pos hpc (measure_ne_top _ _)
    rw [measureReal_compl hP,measureReal_univ_eq_one] at hcpos
    exact ⟨hpos,by linarith⟩
  have hm : unitMeasure P=ENNReal.ofReal (unitMeasure.real P) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hbnd : ∀ᵐ p ∂squareMeasure,bipodalBlockValue P a d b p∈Icc (0:ℝ) 1 := by
    filter_upwards [U.bounded,he] with p hp he
    rwa [← he]
  obtain ⟨ha,hd,hb⟩ := (bipodalBlockValue_ae_iff hP hc hm a d b (fun t => t∈Icc (0:ℝ) 1)).mp hbnd
  exact ⟨a,d,b,isBipodal_of_blockValue hP ha hd hb he⟩

/-- Equality within each row class already implies an actual two-block graphon. -/
theorem bipodal_of_row_class_eq {P : Set ℝ} (hP : MeasurableSet P)
    (hp : unitMeasure P≠0) (hpc : unitMeasure Pᶜ≠0) {U : Graphon}
    (hrows : ∀ᵐ x ∂unitMeasure,∀ᵐ y ∂unitMeasure,
      (x∈P ↔ y∈P) → (fun z => U (x,z)) =ᵐ[unitMeasure] (fun z => U (y,z))) :
    ∃ a d b : ℝ,IsBipodal U (unitMeasure.real P) a d b := by
  have hs := boundedObservable_slices (graphon_boundedObservable U)
  obtain ⟨x,hx,hxr,hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp
    (ae_restrict_of_ae (hrows.and hs))
  obtain ⟨y,hy,hyr,hyb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpc
    (ae_restrict_of_ae (hrows.and hs))
  let f := fun z => U (x,z)
  let g := fun z => U (y,z)
  let K := fun p : ℝ × ℝ => if p.1∈P then f p.2 else g p.2
  have hK : AEMeasurable K squareMeasure := by
    let fm := hxb.measurable.mk f
    let gm := hyb.measurable.mk g
    have hm : Measurable (fun p : ℝ × ℝ => if p.1∈P then fm p.2 else gm p.2) :=
      (hxb.measurable.measurable_mk.comp measurable_snd).ite (hP.preimage measurable_fst)
        (hyb.measurable.measurable_mk.comp measurable_snd)
    apply hm.aemeasurable.congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hxb.measurable.ae_eq_mk,
      Measure.quasiMeasurePreserving_snd.ae hyb.measurable.ae_eq_mk] with p hf hg
    dsimp only [K,fm,gm]
    split_ifs
    · exact hf.symm
    · exact hg.symm
  have he : ∀ᵐ z ∂unitMeasure,∀ᵐ t ∂unitMeasure,U (z,t)=K (z,t) := by
    filter_upwards [hxr,hyr] with z hzx hzy
    by_cases hz : z∈P
    · simpa only [K,f,hz,if_true] using (hzx (iff_of_true hx hz)).symm
    · have hyn : y∉P := hy
      simpa only [K,g,hz,if_false] using (hzy (iff_of_false hyn hz)).symm
  exact bipodal_of_two_rows hP hp hpc (ae_eq_of_ae_rows U.measurable hK he)

/-- Bipodality is unchanged by a.e. replacement. -/
theorem isBipodal_congr {U W : Graphon} {c a d b : ℝ}
    (h : U.toFun =ᵐ[squareMeasure] W.toFun) :
    IsBipodal U c a d b ↔ IsBipodal W c a d b := by
  constructor
  · rintro ⟨hc,ha,hd,hb,P,hP,hsub,hm,he⟩
    exact ⟨hc,ha,hd,hb,P,hP,hsub,hm,h.symm.trans he⟩
  · rintro ⟨hc,ha,hd,hb,P,hP,hsub,hm,he⟩
    exact ⟨hc,ha,hd,hb,P,hP,hsub,hm,h.trans he⟩

/-- Every measure-preserving pullback preserves the two-block parameters. -/
theorem isBipodal_relabel {U : Graphon} {c a d b : ℝ}
    (h : IsBipodal U c a d b) (φ : Relabeling) :
    IsBipodal (relabel U φ) c a d b := by
  obtain ⟨hc,ha,hd,hb,P,hP,hsub,hm,he⟩ := h
  let Q := φ ⁻¹' P
  have hQ : MeasurableSet Q := φ.preserving.measurable hP
  have hmass : unitMeasure.real Q=c := by
    rw [Measure.real,φ.preserving.measure_preimage hP.nullMeasurableSet,hm,
      ENNReal.toReal_ofReal hc.1]
  have he' : (relabel U φ).toFun =ᵐ[squareMeasure] bipodalBlockValue Q a d b := by
    filter_upwards [(φ.preserving.prod φ.preserving).quasiMeasurePreserving.ae he] with p hp
    exact hp
  simpa only [hmass] using isBipodal_of_blockValue hQ ha hd hb he'

/-- For a bijective relabeling the implication also reverses, with no compactness input. -/
theorem isBipodal_relabel_iff (U : Graphon) (φ : BijectiveRelabeling) (c a d b : ℝ) :
    IsBipodal (relabel U φ.toRelabeling) c a d b ↔ IsBipodal U c a d b := by
  constructor
  · intro h
    have hh := isBipodal_relabel h φ.symm.toRelabeling
    have he : (relabel (relabel U φ.toRelabeling) φ.symm.toRelabeling).toFun =ᵐ[squareMeasure] U.toFun :=
      Eventually.of_forall fun p => by
        change U (φ.equiv (φ.equiv.symm p.1),φ.equiv (φ.equiv.symm p.2))=U p
        simp
    exact (isBipodal_congr he).mp hh
  · exact fun h => isBipodal_relabel h φ.toRelabeling

@[simp] theorem blockValue_compl (P : Set ℝ) (a b : ℝ) (p : ℝ × ℝ) :
    blockValue Pᶜ a b p=blockValue P a b p := by
  simp only [blockValue,mem_compl_iff]
  split_ifs <;> rfl

@[simp] theorem blockProfile_compl (P : Set ℝ) (a b x : ℝ) :
    blockProfile Pᶜ a b x=blockProfile P b a x := by
  simp only [blockProfile,mem_compl_iff]
  split_ifs <;> rfl

@[simp] theorem abs_mass_compl_sub_half {P : Set ℝ} (hP : MeasurableSet P) :
    |unitMeasure.real Pᶜ-1/2|=|unitMeasure.real P-1/2| := by
  rw [measureReal_compl hP,measureReal_univ_eq_one]
  have he : (1-unitMeasure.real P)-1/2= -(unitMeasure.real P-1/2) := by ring
  rw [he,abs_neg]

/-- The uniform-neighborhood part of local rigidity. No variational hypothesis
is needed here beyond the actual stationary equations of the rows. -/
theorem exists_uniform_bipodal_radius {a b μ : ℝ} (ha : 0<a) (hab : a<b)
    (hb : b≤1) (hμ : 0<μ) (hEL : BalancedEL a b μ) :
    ∃ δ : ℝ,0<δ ∧ ∀ (P : Set ℝ) (_hP : MeasurableSet P) (ν : ℝ) (U : Graphon),
      0≤ν → |ν-μ|<δ → |unitMeasure.real P-1/2|<δ →
      (∀ᵐ p ∂squareMeasure,|U p-blockValue P a b p|≤δ) →
      (∀ᵐ x ∂unitMeasure,∀ᵐ y ∂unitMeasure,
        Real.log (U (x,y))+ν*rowOperator U (fun z => U (x,z)) y=0) →
      ∃ aa dd bb : ℝ,IsBipodal U (unitMeasure.real P) aa dd bb := by
  obtain ⟨ρ,hρ,heq⟩ := exists_stationary_row_radius ha hab hb hμ hEL
  let δ := min ρ (1/4)
  have hδ : 0<δ := lt_min hρ (by norm_num)
  have hdρ : δ≤ρ := min_le_left _ _
  have hdq : δ≤1/4 := min_le_right _ _
  refine ⟨δ,hδ,?_⟩
  intro P hP ν U hν hνμ hp hU hELU
  have hpρ : |unitMeasure.real P-1/2|<ρ := hp.trans_le hdρ
  have hνρ : |ν-μ|<ρ := hνμ.trans_le hdρ
  have hUρ : ∀ᵐ p ∂squareMeasure,|U p-blockValue P a b p|≤ρ := hU.mono fun _ hx => hx.trans hdρ
  have hp0 : unitMeasure P≠0 := by
    intro hh
    have hh' : unitMeasure.real P=0 := by simp [Measure.real,hh]
    rw [hh'] at hp
    norm_num at hp
    linarith
  have hpc0 : unitMeasure Pᶜ≠0 := by
    intro hh
    have hh' : unitMeasure.real Pᶜ=0 := by simp [Measure.real,hh]
    have hc := measureReal_compl (μ:=unitMeasure) hP
    rw [hh',measureReal_univ_eq_one] at hc
    have hh'' : unitMeasure.real P=1 := by linarith
    rw [hh''] at hp
    norm_num at hp
    linarith
  apply bipodal_of_row_class_eq hP hp0 hpc0
  have hs := boundedObservable_slices (graphon_boundedObservable U)
  have hbnd := Measure.ae_ae_of_ae_prod U.bounded
  have hclose := Measure.ae_ae_of_ae_prod hUρ
  filter_upwards [hs,hbnd,hclose,hELU] with x hmx hbx hcx hEx
  filter_upwards [hs,hbnd,hclose,hELU] with y hmy hby hcy hEy
  intro hxy
  by_cases hx : x∈P
  · have hy : y∈P := hxy.mp hx
    have hfx : ∀ᵐ z ∂unitMeasure,|U (x,z)-blockProfile P a b z|≤ρ := by
      simpa only [blockValue,blockProfile,hx,if_true] using hcx
    have hfy : ∀ᵐ z ∂unitMeasure,|U (y,z)-blockProfile P a b z|≤ρ := by
      simpa only [blockValue,blockProfile,hy,if_true] using hcy
    exact heq P hP ν U (fun z => U (x,z)) (fun z => U (y,z)) hν hνρ hpρ
      hUρ hmx.measurable hmy.measurable hbx hby hfx hfy hEx hEy
  · have hy : y∉P := fun hy => hx (hxy.mpr hy)
    have hfx : ∀ᵐ z ∂unitMeasure,|U (x,z)-blockProfile Pᶜ a b z|≤ρ := by
      simp_rw [blockProfile_compl]
      simpa only [blockValue,blockProfile,hx,if_false] using hcx
    have hfy : ∀ᵐ z ∂unitMeasure,|U (y,z)-blockProfile Pᶜ a b z|≤ρ := by
      simp_rw [blockProfile_compl]
      simpa only [blockValue,blockProfile,hy,if_false] using hcy
    have hUc : ∀ᵐ p ∂squareMeasure,|U p-twoBlock Pᶜ hP.compl a b
        ⟨ha.le,hab.le.trans hb⟩ ⟨(ha.trans hab).le,hb⟩ p|≤ρ := by
      change ∀ᵐ p ∂squareMeasure,|U p-blockValue Pᶜ a b p|≤ρ
      simpa only [blockValue_compl] using hUρ
    exact heq Pᶜ hP.compl ν U (fun z => U (x,z)) (fun z => U (y,z)) hν hνρ
      (by simpa only [abs_mass_compl_sub_half hP] using hpρ)
      hUc hmx.measurable hmy.measurable hbx hby hfx hfy hEx hEy

end SparseLowerTail.Section06
