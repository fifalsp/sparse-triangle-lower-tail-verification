import SparseLowerTail.Section05.CriticalCoverGeometry

/-! Exact JSON multipliers, support cutoffs and coordinate minima. All fields
of VerifiedCertificateCell other than certificate positivity are proved here. -/
noncomputable section
open Set
namespace SparseLowerTail.Section05.CoverGeometry
open Section04 Numerics

def cellLambda : Fin 12 → ℝ := ![(1943303239210369/2251799813685248:ℝ),
  (7962364141191037/9007199254740992:ℝ),
  (255297803876565/281474976710656:ℝ),
  (8782019273372467/9007199254740992:ℝ),
  (5368290755825631/9007199254740992:ℝ),
  (0/1:ℝ),
  (1080863910568919/1125899906842624:ℝ),
  (1048212813270483/1125899906842624:ℝ),
  (3859584880656515/4503599627370496:ℝ),
  (5908722711110091/36028797018963968:ℝ),
  (1/1:ℝ),
  (1206964700135293/4503599627370496:ℝ)]

def cellQ : Fin 12 → ℝ := ![(3287/512:ℝ),
  (7377/1024:ℝ),
  (2021/256:ℝ),
  (491/64:ℝ),
  (1729/256:ℝ),
  (2893/512:ℝ),
  (6743/512:ℝ),
  (2773/256:ℝ),
  (285/32:ℝ),
  (1607/256:ℝ),
  (9009/512:ℝ),
  (4629/256:ℝ)]

def cellMeanLower : Fin 12 → ℝ := ![(934947282642115/2251799813685248:ℝ),
  (3676738735785273/9007199254740992:ℝ),
  (3676738735785273/9007199254740992:ℝ),
  (1860887366029489/4503599627370496:ℝ),
  (43319048169/100000000000:ℝ),
  (43319048169/100000000000:ℝ),
  (7872292148643627/36028797018963968:ℝ),
  (5944751508129055/18014398509481984:ℝ),
  (3422735716801577/9007199254740992:ℝ),
  (7983981419402415/18014398509481984:ℝ),
  (7872292148643627/36028797018963968:ℝ),
  (5944751508129055/18014398509481984:ℝ)]

def cellCostLower : Fin 12 → ℝ := ![(4150517416584649/9007199254740992:ℝ),
  (4078459822546721/9007199254740992:ℝ),
  (248429814444825/562949953421312:ℝ),
  (248429814444825/562949953421312:ℝ),
  (248429814444825/562949953421312:ℝ),
  (1035377554332477/2251799813685248:ℝ),
  (8304637712871195/18014398509481984:ℝ),
  (4003700068732371/9007199254740992:ℝ),
  (4003700068732371/9007199254740992:ℝ),
  (248429814444825/562949953421312:ℝ),
  (3512807709348987/9007199254740992:ℝ),
  (6034823500676465/18014398509481984:ℝ)]

theorem criticalMean_sharp_lower : (43319048169/100000000000:ℝ)≤criticalMean := by
  unfold criticalMean
  have ha : (1703401908/10^11:ℝ) ≤ criticalA := transition_digits.1.1
  have hb : (8493469443/10^10:ℝ) ≤ criticalB := transition_digits.2.1.1
  linarith

theorem cellLambda_nonneg (i : Fin 12) : 0≤cellLambda i := by
  fin_cases i
  · change 0≤(1943303239210369/2251799813685248:ℝ)
    norm_num
  · change 0≤(7962364141191037/9007199254740992:ℝ)
    norm_num
  · change 0≤(255297803876565/281474976710656:ℝ)
    norm_num
  · change 0≤(8782019273372467/9007199254740992:ℝ)
    norm_num
  · change 0≤(5368290755825631/9007199254740992:ℝ)
    norm_num
  · change 0≤(0/1:ℝ)
    norm_num
  · change 0≤(1080863910568919/1125899906842624:ℝ)
    norm_num
  · change 0≤(1048212813270483/1125899906842624:ℝ)
    norm_num
  · change 0≤(3859584880656515/4503599627370496:ℝ)
    norm_num
  · change 0≤(5908722711110091/36028797018963968:ℝ)
    norm_num
  · change 0≤(1/1:ℝ)
    norm_num
  · change 0≤(1206964700135293/4503599627370496:ℝ)
    norm_num

theorem cellMeanLower_pos (i : Fin 12) : 0<cellMeanLower i := by
  fin_cases i
  · change 0<(934947282642115/2251799813685248:ℝ)
    norm_num
  · change 0<(3676738735785273/9007199254740992:ℝ)
    norm_num
  · change 0<(3676738735785273/9007199254740992:ℝ)
    norm_num
  · change 0<(1860887366029489/4503599627370496:ℝ)
    norm_num
  · change 0<(43319048169/100000000000:ℝ)
    norm_num
  · change 0<(43319048169/100000000000:ℝ)
    norm_num
  · change 0<(7872292148643627/36028797018963968:ℝ)
    norm_num
  · change 0<(5944751508129055/18014398509481984:ℝ)
    norm_num
  · change 0<(3422735716801577/9007199254740992:ℝ)
    norm_num
  · change 0<(7983981419402415/18014398509481984:ℝ)
    norm_num
  · change 0<(7872292148643627/36028797018963968:ℝ)
    norm_num
  · change 0<(5944751508129055/18014398509481984:ℝ)
    norm_num

theorem cellCostLower_lt_one (i : Fin 12) : cellCostLower i<1 := by
  fin_cases i
  · change (4150517416584649/9007199254740992:ℝ)<1
    norm_num
  · change (4078459822546721/9007199254740992:ℝ)<1
    norm_num
  · change (248429814444825/562949953421312:ℝ)<1
    norm_num
  · change (248429814444825/562949953421312:ℝ)<1
    norm_num
  · change (248429814444825/562949953421312:ℝ)<1
    norm_num
  · change (1035377554332477/2251799813685248:ℝ)<1
    norm_num
  · change (8304637712871195/18014398509481984:ℝ)<1
    norm_num
  · change (4003700068732371/9007199254740992:ℝ)<1
    norm_num
  · change (4003700068732371/9007199254740992:ℝ)<1
    norm_num
  · change (248429814444825/562949953421312:ℝ)<1
    norm_num
  · change (3512807709348987/9007199254740992:ℝ)<1
    norm_num
  · change (6034823500676465/18014398509481984:ℝ)<1
    norm_num

theorem cell_coordinate_lower (i : Fin 12) :
    ∀ v∈cellVertices i,cellMeanLower i≤v.1 ∧ cellCostLower i≤v.2 := by
  have hm := criticalMean_sharp_lower
  have hF := criticalPoint_box.2.2.1
  fin_cases i
  · change ∀ v∈({criticalPoint,((3766810728332683/9007199254740992:ℝ),(8336703342218073/18014398509481984:ℝ)),((934947282642115/2251799813685248:ℝ),(4150517416584649/9007199254740992:ℝ))}:Finset (ℝ×ℝ)),(934947282642115/2251799813685248:ℝ)≤v.1 ∧ (4150517416584649/9007199254740992:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({criticalPoint,((934947282642115/2251799813685248:ℝ),(4150517416584649/9007199254740992:ℝ)),((3676738735785273/9007199254740992:ℝ),(4078459822546721/9007199254740992:ℝ))}:Finset (ℝ×ℝ)),(3676738735785273/9007199254740992:ℝ)≤v.1 ∧ (4078459822546721/9007199254740992:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({criticalPoint,((3676738735785273/9007199254740992:ℝ),(4078459822546721/9007199254740992:ℝ)),((1860887366029489/4503599627370496:ℝ),(248429814444825/562949953421312:ℝ))}:Finset (ℝ×ℝ)),(3676738735785273/9007199254740992:ℝ)≤v.1 ∧ (248429814444825/562949953421312:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({criticalPoint,((1860887366029489/4503599627370496:ℝ),(248429814444825/562949953421312:ℝ)),((8164125404497235/18014398509481984:ℝ),(248429814444825/562949953421312:ℝ))}:Finset (ℝ×ℝ)),(1860887366029489/4503599627370496:ℝ)≤v.1 ∧ (248429814444825/562949953421312:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({criticalPoint,((8164125404497235/18014398509481984:ℝ),(248429814444825/562949953421312:ℝ)),((8020010216421379/18014398509481984:ℝ),(1035377554332477/2251799813685248:ℝ))}:Finset (ℝ×ℝ)),(43319048169/100000000000:ℝ)≤v.1 ∧ (248429814444825/562949953421312:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({criticalPoint,((8020010216421379/18014398509481984:ℝ),(1035377554332477/2251799813685248:ℝ)),((7983981419402415/18014398509481984:ℝ),(4169432535019605/9007199254740992:ℝ))}:Finset (ℝ×ℝ)),(43319048169/100000000000:ℝ)≤v.1 ∧ (1035377554332477/2251799813685248:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change _≤criticalMean ∧ _≤criticalCost
      constructor <;> linarith
    · norm_num
    · norm_num
  · change ∀ v∈({((7872292148643627/36028797018963968:ℝ),(8304637712871195/18014398509481984:ℝ)),((5944751508129055/18014398509481984:ℝ),(8304637712871195/18014398509481984:ℝ)),((5944751508129055/18014398509481984:ℝ),(8336703342218073/18014398509481984:ℝ)),((7872292148643627/36028797018963968:ℝ),(8336703342218073/18014398509481984:ℝ))}:Finset (ℝ×ℝ)),(7872292148643627/36028797018963968:ℝ)≤v.1 ∧ (8304637712871195/18014398509481984:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · change ∀ v∈({((5944751508129055/18014398509481984:ℝ),(4003700068732371/9007199254740992:ℝ)),((3422735716801577/9007199254740992:ℝ),(4003700068732371/9007199254740992:ℝ)),((3422735716801577/9007199254740992:ℝ),(8336703342218073/18014398509481984:ℝ)),((5944751508129055/18014398509481984:ℝ),(8336703342218073/18014398509481984:ℝ))}:Finset (ℝ×ℝ)),(5944751508129055/18014398509481984:ℝ)≤v.1 ∧ (4003700068732371/9007199254740992:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · change ∀ v∈({((3422735716801577/9007199254740992:ℝ),(4003700068732371/9007199254740992:ℝ)),((3766810728332683/9007199254740992:ℝ),(4003700068732371/9007199254740992:ℝ)),((3766810728332683/9007199254740992:ℝ),(8336703342218073/18014398509481984:ℝ)),((3422735716801577/9007199254740992:ℝ),(8336703342218073/18014398509481984:ℝ))}:Finset (ℝ×ℝ)),(3422735716801577/9007199254740992:ℝ)≤v.1 ∧ (4003700068732371/9007199254740992:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · change ∀ v∈({((8164125404497235/18014398509481984:ℝ),(248429814444825/562949953421312:ℝ)),((2296835809958953/4503599627370496:ℝ),(248429814444825/562949953421312:ℝ)),((2296835809958953/4503599627370496:ℝ),(4169432535019605/9007199254740992:ℝ)),((7983981419402415/18014398509481984:ℝ),(4169432535019605/9007199254740992:ℝ))}:Finset (ℝ×ℝ)),(7983981419402415/18014398509481984:ℝ)≤v.1 ∧ (248429814444825/562949953421312:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · change ∀ v∈({((7872292148643627/36028797018963968:ℝ),(3512807709348987/9007199254740992:ℝ)),((5944751508129055/18014398509481984:ℝ),(3512807709348987/9007199254740992:ℝ)),((5944751508129055/18014398509481984:ℝ),(519602807007871/1125899906842624:ℝ)),((7872292148643627/36028797018963968:ℝ),(519602807007871/1125899906842624:ℝ))}:Finset (ℝ×ℝ)),(7872292148643627/36028797018963968:ℝ)≤v.1 ∧ (3512807709348987/9007199254740992:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · change ∀ v∈({((5944751508129055/18014398509481984:ℝ),(6034823500676465/18014398509481984:ℝ)),((2296835809958953/4503599627370496:ℝ),(6034823500676465/18014398509481984:ℝ)),((2296835809958953/4503599627370496:ℝ),(8016407336719483/18014398509481984:ℝ)),((5944751508129055/18014398509481984:ℝ),(8016407336719483/18014398509481984:ℝ))}:Finset (ℝ×ℝ)),(5944751508129055/18014398509481984:ℝ)≤v.1 ∧ (6034823500676465/18014398509481984:ℝ)≤v.2
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num

/-- Every exact support cutoff dominates the true support exponent at the
conservative cell minima. This is rational arithmetic plus t*'s checked bound. -/
theorem cell_supportExponent_le (i : Fin 12) :
    supportExponent criticalTriangle (cellMeanLower i) (cellCostLower i)≤cellQ i := by
  have ht := criticalTriangle_sharp_bounds.1
  have ht0 : 0<criticalTriangle := lt_of_lt_of_le (by norm_num) ht
  unfold supportExponent
  apply (div_le_iff₀ (mul_pos (by norm_num) ht0)).mpr
  fin_cases i
  · change (1-(4150517416584649/9007199254740992:ℝ))^2-(934947282642115/2251799813685248:ℝ)^2≤(3287/512:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(4078459822546721/9007199254740992:ℝ))^2-(3676738735785273/9007199254740992:ℝ)^2≤(7377/1024:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(248429814444825/562949953421312:ℝ))^2-(3676738735785273/9007199254740992:ℝ)^2≤(2021/256:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(248429814444825/562949953421312:ℝ))^2-(1860887366029489/4503599627370496:ℝ)^2≤(491/64:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(248429814444825/562949953421312:ℝ))^2-(43319048169/100000000000:ℝ)^2≤(1729/256:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(1035377554332477/2251799813685248:ℝ))^2-(43319048169/100000000000:ℝ)^2≤(2893/512:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(8304637712871195/18014398509481984:ℝ))^2-(7872292148643627/36028797018963968:ℝ)^2≤(6743/512:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(4003700068732371/9007199254740992:ℝ))^2-(5944751508129055/18014398509481984:ℝ)^2≤(2773/256:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(4003700068732371/9007199254740992:ℝ))^2-(3422735716801577/9007199254740992:ℝ)^2≤(285/32:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(248429814444825/562949953421312:ℝ))^2-(7983981419402415/18014398509481984:ℝ)^2≤(1607/256:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(3512807709348987/9007199254740992:ℝ))^2-(7872292148643627/36028797018963968:ℝ)^2≤(9009/512:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]
  · change (1-(6034823500676465/18014398509481984:ℝ))^2-(5944751508129055/18014398509481984:ℝ)^2≤(4629/256:ℝ)*(2*criticalTriangle)
    nlinarith only [ht]

/-- The canonical cells. The coefficient arrays are supplied separately so that
proving each nonlinear certificate remains an explicit task. -/
def certificateCell (theta : Fin 12 → Fin 12 → ℝ) (i : Fin 12) : CertificateCell where
  vertices := cellVertices i
  theta := theta i
  lam := cellLambda i
  Q := cellQ i
  meanLower := cellMeanLower i
  costLower := cellCostLower i

/-- All geometric/support bookkeeping is discharged; only the actual nonlinear
vertex and apex inequalities remain in this certificate interface. -/
theorem verifiedCover_of_positivity (theta : Fin 12 → Fin 12 → ℝ)
    (hvertex : ∀ i v,v∈cellVertices i → v≠criticalPoint →
      ∀ u∈edgeCube (Real.exp (-cellQ i)),0<coverCertificate (theta i) (cellLambda i) u v)
    (hapex : ∀ i,criticalPoint∈cellVertices i →
      ∀ u∈edgeCube (Real.exp (-cellQ i)),0≤coverCertificate (theta i) (cellLambda i) u criticalPoint) :
    VerifiedCertificateCover (certificateCell theta) := by
  constructor
  · intro i
    exact ⟨cellLambda_nonneg i,cellMeanLower_pos i,cellCostLower_lt_one i,
      fun v hv => (cell_coordinate_lower i v hv).1,
      fun v hv => (cell_coordinate_lower i v hv).2,
      cell_supportExponent_le i,hvertex i,hapex i⟩
  · exact covers_of_vertices (certificateCell theta) (fun _ => rfl)

end SparseLowerTail.Section05.CoverGeometry
