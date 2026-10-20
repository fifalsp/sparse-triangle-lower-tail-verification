import SparseLowerTail.Section05.PlanarConvex
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The ray-exit and height arguments for a polygon fan, including boundary cases. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SparseLowerTail.Section05.Planar

/-- A ray through a point of a compact set meets its boundary beyond that point. -/
theorem compact_ray_exit {W : Set (ℝ × ℝ)} (hW : IsCompact W)
    {A p : ℝ × ℝ} (hp : p ∈ W) (hne : p ≠ A) :
    ∃ q ∈ frontier W,p ∈ segment ℝ A q := by
  let F : ℝ → ℝ × ℝ := fun t => A+t • (p-A)
  have hc : Continuous F := continuous_const.add (continuous_id.smul continuous_const)
  let T : Set ℝ := Ici 1 ∩ F ⁻¹' W
  have hT1 : (1:ℝ) ∈ T := by simpa [T,F] using hp
  have hd : 0<‖p-A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨R,hR,hbound⟩ := hW.isBounded.exists_pos_norm_lt
  have hTb : BddAbove T := by
    refine ⟨(R+‖A‖)/‖p-A‖,?_⟩
    intro t ht
    have ht0 : 0≤t := (by norm_num : (0:ℝ)≤1).trans ht.1
    have hnorm : t*‖p-A‖<R+‖A‖ := by
      calc
        _=‖F t-A‖ := by simp [F,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
        _≤‖F t‖+‖A‖ := norm_sub_le _ _
        _<R+‖A‖ := add_lt_add_right (hbound _ ht.2) _
    exact ((lt_div_iff₀ hd).mpr hnorm).le
  have hTc : IsClosed T := isClosed_Ici.inter (hW.isClosed.preimage hc)
  have ht : sSup T ∈ T := hTc.csSup_mem ⟨1,hT1⟩ hTb
  have hq : F (sSup T) ∈ frontier W := by
    refine ⟨subset_closure ht.2,?_⟩
    intro hi
    have hnear : ∀ᶠ t in 𝓝 (sSup T),F t ∈ W :=
      hc.continuousAt.eventually_mem (mem_interior_iff_mem_nhds.mp hi)
    obtain ⟨t,htt,hFt⟩ := ((show ∀ᶠ t in 𝓝[>] (sSup T),sSup T<t from
      self_mem_nhdsWithin).and (hnear.filter_mono nhdsWithin_le_nhds)).exists
    have hh : t≤sSup T := le_csSup hTb ⟨ht.1.trans htt.le,hFt⟩
    linarith
  refine ⟨F (sSup T),hq,?_⟩
  have htpos : 0<sSup T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ht.1
  refine ⟨1-1/sSup T,1/sSup T,sub_nonneg.mpr ((div_le_one₀ htpos).mpr ht.1),
    by positivity,by ring,?_⟩
  ext <;> simp only [F,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> field_simp [htpos.ne'] <;> ring

/-- Points below the apex in the closing triangle are exactly the apex. -/
theorem closing_triangle_height {A B C p : ℝ × ℝ} (hB : A.2<B.2) (hC : A.2<C.2)
    (hp : p ∈ convexHull ℝ ({A,B,C} : Set (ℝ × ℝ))) (hy : p.2≤A.2) : p=A := by
  rw [convexHull_insert (insert_nonempty B {C}),convexHull_pair,mem_convexJoin] at hp
  obtain ⟨a,ha,q,hq,hpq⟩ := hp
  have haA : a=A := mem_singleton_iff.mp ha
  subst a
  obtain ⟨s,t,hs,ht,hst,hq⟩ := hq
  have hq2 := congrArg Prod.snd hq
  simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul] at hq2
  have hqy : A.2<q.2 := by
    rcases eq_or_lt_of_le hs with hs0|hspos
    · have ht1 : t=1 := by linarith
      rw [← hs0,ht1] at hq2
      simp only [zero_mul,one_mul,zero_add] at hq2
      exact hC.trans_eq hq2
    · have h1 := mul_pos hspos (sub_pos.mpr hB)
      have h2 := mul_nonneg ht (sub_nonneg.mpr hC.le)
      nlinarith [congrArg (fun a : ℝ => a*A.2) hst]
  obtain ⟨u,v,hu,hv,huv,hp⟩ := hpq
  have hp2 := congrArg Prod.snd hp
  simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul] at hp2
  have hv0 : v=0 := by
    by_contra hn
    have hpv := mul_pos (lt_of_le_of_ne hv (Ne.symm hn)) (sub_pos.mpr hqy)
    nlinarith [congrArg (fun a : ℝ => a*A.2) huv]
  have hu1 : u=1 := by linarith
  simpa [hv0,hu1] using hp.symm

/-- A cyclic boundary-edge presentation is the ordinary data of a closed convex polygon. -/
structure PolygonBoundary (n : ℕ) where
  region : Set (ℝ × ℝ)
  vertex : Fin (n+1) → ℝ × ℝ
  vertex_mem : ∀ i,vertex i ∈ region
  region_hull : region=convexHull ℝ (Set.range vertex)
  compact : IsCompact region
  convex : Convex ℝ region
  boundary_edges : frontier region=⋃ i : Fin (n+1),segment ℝ (vertex i) (vertex (i+1))

/-- All edge triangles cover a polygon, by an actual ray exit through its boundary. -/
theorem PolygonBoundary.mem_full_fan {n : ℕ} (P : PolygonBoundary n)
    (A : ℝ × ℝ) {p : ℝ × ℝ} (hp : p ∈ P.region) :
    ∃ i : Fin (n+1),p ∈ convexHull ℝ ({A,P.vertex i,P.vertex (i+1)} : Set (ℝ × ℝ)) := by
  by_cases h : p=A
  · refine ⟨0,?_⟩
    rw [h]
    exact subset_convexHull ℝ _ (by simp)
  obtain ⟨q,hq,hpq⟩ := compact_ray_exit P.compact hp h
  rw [P.boundary_edges] at hq
  obtain ⟨i,hi⟩ := mem_iUnion.mp hq
  refine ⟨i,?_⟩
  have hv : segment ℝ (P.vertex i) (P.vertex (i+1)) ⊆
      convexHull ℝ ({A,P.vertex i,P.vertex (i+1)} : Set (ℝ × ℝ)) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by intro x hx;simp only [mem_insert_iff,mem_singleton_iff] at *;tauto)
  exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp)) (hv hi) hpq


/-- The generic polygon fan lemma: the top closing triangle may be omitted below A. -/
theorem PolygonBoundary.mem_lower_fan {n : ℕ} (hn : 2≤n) (P : PolygonBoundary n)
    (A : ℝ × ℝ) (_hA : A ∈ P.region) (hfirst : A.2<(P.vertex 0).2)
    (hlast : A.2<(P.vertex (Fin.last n)).2) {p : ℝ × ℝ}
    (hp : p ∈ P.region) (hy : p.2≤A.2) :
    ∃ i : Fin n,p ∈ convexHull ℝ ({A,P.vertex i.castSucc,P.vertex i.succ} : Set (ℝ × ℝ)) := by
  obtain ⟨i,hi⟩ := P.mem_full_fan A hp
  by_cases he : i=Fin.last n
  · have hc : (Fin.last n : Fin (n+1))+1=0 := by
      apply Fin.ext
      simp
    have hpA : p=A := closing_triangle_height hlast hfirst (by simpa [he,hc] using hi) hy
    refine ⟨⟨0,by omega⟩,?_⟩
    rw [hpA]
    exact subset_convexHull ℝ _ (by simp)
  · have hin : i.val<n := by
      have hb := i.isLt
      have hne : i.val≠n := by
        intro h
        apply he
        exact Fin.ext h
      omega
    let j : Fin n := ⟨i.val,hin⟩
    have hj : j.castSucc=i := Fin.ext rfl
    have hj1 : j.succ=i+1 := by
      apply Fin.ext
      simp only [Fin.val_add]
      change i.val+1=(i.val+1%(n+1))%(n+1)
      rw [Nat.mod_eq_of_lt (show 1<n+1 by omega),Nat.mod_eq_of_lt (show i.val+1<n+1 by omega)]
    exact ⟨j,by simpa only [hj,hj1] using hi⟩

end SparseLowerTail.Section05.Planar
