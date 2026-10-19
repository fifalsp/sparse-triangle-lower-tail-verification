import SparseLowerTail.Triangle
import SparseLowerTail.Section08.GraphonIntegration

/-! Measurable, everywhere bounded symmetric representatives for insertion
variations. All variational quantities are preserved by the proved a.e. equality. -/
noncomputable section
open MeasureTheory Set
namespace SparseLowerTail.Section06

/-- An everywhere version of a graphon, useful on enlarged vertex spaces. -/
structure PointwiseGraphon where
  toFun : ℝ × ℝ → ℝ
  measurable : Measurable toFun
  symmetric : ∀ p, toFun p.swap=toFun p
  bounded : ∀ p, toFun p ∈ Icc (0:ℝ) 1

instance : CoeFun PointwiseGraphon (fun _ => ℝ × ℝ → ℝ) := ⟨PointwiseGraphon.toFun⟩

def PointwiseGraphon.toGraphon (U : PointwiseGraphon) : Graphon where
  toFun := U.toFun
  measurable := U.measurable.aemeasurable
  symmetric := Filter.Eventually.of_forall U.symmetric
  bounded := Filter.Eventually.of_forall U.bounded

def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clampUnit_mem (x : ℝ) : clampUnit x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clampUnit_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : clampUnit x=x := by
  simp [clampUnit,min_eq_right hx.2,max_eq_right hx.1]

theorem measurable_clampUnit : Measurable clampUnit :=
  measurable_const.max (measurable_const.min measurable_id)

/-- Clamp a measurable representative and symmetrize it. -/
def pointwiseRepresentative (U : Graphon) : PointwiseGraphon where
  toFun p := (clampUnit (U.measurable.mk U.toFun p)+
    clampUnit (U.measurable.mk U.toFun p.swap))/2
  measurable := ((measurable_clampUnit.comp U.measurable.measurable_mk).add
    (measurable_clampUnit.comp (U.measurable.measurable_mk.comp measurable_swap))).div_const 2
  symmetric p := by simp only [Prod.swap_swap]; ring
  bounded p := by
    have h1 := clampUnit_mem (U.measurable.mk U.toFun p)
    have h2 := clampUnit_mem (U.measurable.mk U.toFun p.swap)
    constructor <;> dsimp <;> linarith [h1.1,h1.2,h2.1,h2.2]

theorem pointwiseRepresentative_ae (U : Graphon) :
    (pointwiseRepresentative U).toFun =ᵐ[squareMeasure] U.toFun := by
  have he := U.measurable.ae_eq_mk
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae he
  filter_upwards [he,hs,U.symmetric,U.bounded] with p hp hq hsym hb
  change (clampUnit (U.measurable.mk U.toFun p)+
    clampUnit (U.measurable.mk U.toFun p.swap))/2=U p
  rw [← hp,← hq,hsym,clampUnit_eq hb]
  ring

theorem PointwiseGraphon.boundedObservable (U : PointwiseGraphon)
    (μ : Measure (ℝ × ℝ)) : BoundedObservable μ U.toFun := by
  refine ⟨U.measurable.aemeasurable,1,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (U.bounded p).1]
  exact (U.bounded p).2

end SparseLowerTail.Section06
