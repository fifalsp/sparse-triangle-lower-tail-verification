import SparseLowerTail.Section05.LogBoxSubdivision

/-! Exact geometry shared by every logarithmic Taylor box. -/
noncomputable section
namespace SparseLowerTail.Section05

/-- The midpoint is represented using rational arithmetic before casting. -/
def LogBox.centerCoordinate (B : LogBox) (i : Fin 3) : ℚ := (B.lower i+B.upper i)/2

def LogBox.radius (B : LogBox) (i : Fin 3) : ℚ := (B.upper i-B.lower i)/2

def LogBox.center (B : LogBox) : EdgeTriple :=
  (((B.centerCoordinate 0 : ℝ),(B.centerCoordinate 1 : ℝ)),(B.centerCoordinate 2 : ℝ))

def LogBox.displacement (B : LogBox) (q : EdgeTriple) : EdgeTriple :=
  ((q.1.1-(B.center).1.1,q.1.2-(B.center).1.2),q.2-(B.center).2)

def edgeLine (c v : EdgeTriple) (s : ℝ) : EdgeTriple :=
  ((c.1.1+s*v.1.1,c.1.2+s*v.1.2),c.2+s*v.2)

@[simp] theorem LogBox.coordinate_center (B : LogBox) (i : Fin 3) :
    edgeCoordinate B.center i=(B.centerCoordinate i : ℝ) := by fin_cases i <;> rfl

@[simp] theorem LogBox.coordinate_displacement (B : LogBox) (q : EdgeTriple) (i : Fin 3) :
    edgeCoordinate (B.displacement q) i=edgeCoordinate q i-(B.centerCoordinate i : ℝ) := by
  fin_cases i <;> rfl

@[simp] theorem edgeCoordinate_line (c v : EdgeTriple) (s : ℝ) (i : Fin 3) :
    edgeCoordinate (edgeLine c v s) i=edgeCoordinate c i+s*edgeCoordinate v i := by
  fin_cases i <;> rfl

/-- Nonemptiness automatically supplies the endpoint ordering. -/
theorem LogBox.ordered_of_mem {B : LogBox} {q : EdgeTriple} (hq : q∈B.region) :
    ∀ i,B.lower i≤B.upper i := by
  intro i
  exact_mod_cast (hq i).1.trans (hq i).2

theorem LogBox.radius_nonneg {B : LogBox} (hB : ∀ i,B.lower i≤B.upper i) (i : Fin 3) :
    0≤B.radius i := by dsimp [LogBox.radius]; linarith [hB i]

theorem LogBox.center_mem {B : LogBox} (hB : ∀ i,B.lower i≤B.upper i) :
    B.center∈B.region := by
  intro i
  rw [B.coordinate_center]
  have h : (B.lower i : ℝ)≤(B.upper i : ℝ) := by exact_mod_cast hB i
  dsimp [LogBox.centerCoordinate]
  push_cast
  constructor <;> linarith

/-- Every displacement lies in the symmetric rational radius interval. -/
theorem LogBox.displacement_bounds {B : LogBox} {q : EdgeTriple} (hq : q∈B.region)
    (i : Fin 3) :
    -(B.radius i : ℝ)≤edgeCoordinate (B.displacement q) i ∧
      edgeCoordinate (B.displacement q) i≤(B.radius i : ℝ) := by
  rw [B.coordinate_displacement]
  dsimp [LogBox.radius,LogBox.centerCoordinate]
  push_cast
  constructor <;> linarith [(hq i).1,(hq i).2]

theorem LogBox.abs_displacement_le {B : LogBox} {q : EdgeTriple} (hq : q∈B.region)
    (i : Fin 3) : |edgeCoordinate (B.displacement q) i|≤(B.radius i : ℝ) :=
  abs_le.mpr (B.displacement_bounds hq i)

/-- The entire segment from the center to a box point stays in the box. -/
theorem LogBox.segment_mem {B : LogBox} {q : EdgeTriple} (hq : q∈B.region)
    {s : ℝ} (hs : s∈Set.Icc (0:ℝ) 1) :
    edgeLine B.center (B.displacement q) s∈B.region := by
  have hc := B.center_mem (B.ordered_of_mem hq)
  intro i
  rw [edgeCoordinate_line,B.coordinate_displacement,←B.coordinate_center]
  have hlo := mul_nonneg hs.1 (sub_nonneg.mpr (hq i).1)
  have hhi := mul_nonneg hs.1 (sub_nonneg.mpr (hq i).2)
  have hlo' := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hc i).1)
  have hhi' := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hc i).2)
  constructor <;> nlinarith

@[simp] theorem edgeLine_zero (c v : EdgeTriple) : edgeLine c v 0=c := by
  simp [edgeLine]

@[simp] theorem LogBox.segment_one (B : LogBox) (q : EdgeTriple) :
    edgeLine B.center (B.displacement q) 1=q := by simp [edgeLine,LogBox.displacement]

end SparseLowerTail.Section05
