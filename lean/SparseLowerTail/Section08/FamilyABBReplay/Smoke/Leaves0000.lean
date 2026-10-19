import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Parameter0000
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Parameter0001
import SparseLowerTail.Section08.FamilyABBReplay.Smoke.Endpoints0000

/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace SparseLowerTail.Section08.FamilyABBReplay.Smoke
open SparseLowerTail.Numerics
open SparseLowerTail.Certificate SparseLowerTail.Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def offsetBox0 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-3/32 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)]⟩
def box0 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp39,exp4,exp4],![exp43,exp10,exp10]⟩
theorem box0_valid : box0.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp39_valid
    · exact exp4_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp43_valid
    · exact exp10_valid
    · exact exp10_valid
def certificate0 : FamilyScaledBoxCertificate := ⟨box0,![![exp39,exp20,exp20],![exp20,exp4,exp4],![exp20,exp4,exp4]],![![exp43,exp28,exp28],![exp28,exp10,exp10],![exp28,exp10,exp10]]⟩
theorem certificate0_valid : certificate0.Valid := by
  refine ⟨box0_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
def transform0 : FamilyRationalMatrix := ![![(1603753/1000000 : ℚ),(-22317/40000 : ℚ),(-215637/125000 : ℚ)],![(0/1 : ℚ),(4451249/1000000 : ℚ),(30809/5000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7601407/1000000 : ℚ)]]
theorem margins0 : FamilyIntervalPositive (familyIntervalCongruence certificate0.hessianIntervals transform0) := by decide +kernel
theorem enclosure0 : box0.EnclosesABBOffsets offsetBox0 := by decide +kernel
theorem conclusion0 : ∀x,offsetBox0.Contains x → familyABBOffsetProperty x :=
  certificate0.abb_offset_property certificate0_valid transform0 margins0 enclosure0

def offsetBox1 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-3/32 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)]⟩
def box1 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp40,exp4,exp4],![exp45,exp10,exp10]⟩
theorem box1_valid : box1.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp40_valid
    · exact exp4_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp45_valid
    · exact exp10_valid
    · exact exp10_valid
def certificate1 : FamilyScaledBoxCertificate := ⟨box1,![![exp40,exp21,exp21],![exp21,exp4,exp4],![exp21,exp4,exp4]],![![exp45,exp29,exp29],![exp29,exp10,exp10],![exp29,exp10,exp10]]⟩
theorem certificate1_valid : certificate1.Valid := by
  refine ⟨box1_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
def transform1 : FamilyRationalMatrix := ![![(321109/200000 : ℚ),(-277541/500000 : ℚ),(-858121/500000 : ℚ)],![(0/1 : ℚ),(4451103/1000000 : ℚ),(6161313/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(237529/31250 : ℚ)]]
theorem margins1 : FamilyIntervalPositive (familyIntervalCongruence certificate1.hessianIntervals transform1) := by decide +kernel
theorem enclosure1 : box1.EnclosesABBOffsets offsetBox1 := by decide +kernel
theorem conclusion1 : ∀x,offsetBox1.Contains x → familyABBOffsetProperty x :=
  certificate1.abb_offset_property certificate1_valid transform1 margins1 enclosure1

def offsetBox2 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(251/64 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)]⟩
def box2 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp41,exp3,exp3],![exp46,exp9,exp9]⟩
theorem box2_valid : box2.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp41_valid
    · exact exp3_valid
    · exact exp3_valid
  · intro j; fin_cases j
    · exact exp46_valid
    · exact exp9_valid
    · exact exp9_valid
def certificate2 : FamilyScaledBoxCertificate := ⟨box2,![![exp41,exp22,exp22],![exp22,exp3,exp3],![exp22,exp3,exp3]],![![exp46,exp31,exp31],![exp31,exp9,exp9],![exp31,exp9,exp9]]⟩
theorem certificate2_valid : certificate2.Valid := by
  refine ⟨box2_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp3_valid,exp9_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp3_valid,exp9_valid,by decide +kernel,by decide +kernel⟩
def transform2 : FamilyRationalMatrix := ![![(80117/50000 : ℚ),(-552343/1000000 : ℚ),(-84529/50000 : ℚ)],![(0/1 : ℚ),(2225269/500000 : ℚ),(6083937/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7538009/1000000 : ℚ)]]
theorem margins2 : FamilyIntervalPositive (familyIntervalCongruence certificate2.hessianIntervals transform2) := by decide +kernel
theorem enclosure2 : box2.EnclosesABBOffsets offsetBox2 := by decide +kernel
theorem conclusion2 : ∀x,offsetBox2.Contains x → familyABBOffsetProperty x :=
  certificate2.abb_offset_property certificate2_valid transform2 margins2 enclosure2

def offsetBox3 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-3/32 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ)]⟩
def box3 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp39,exp4,exp8],![exp43,exp10,exp14]⟩
theorem box3_valid : box3.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp39_valid
    · exact exp4_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp43_valid
    · exact exp10_valid
    · exact exp14_valid
def certificate3 : FamilyScaledBoxCertificate := ⟨box3,![![exp39,exp20,exp23],![exp20,exp4,exp6],![exp23,exp6,exp8]],![![exp43,exp28,exp30],![exp28,exp10,exp12],![exp30,exp12,exp14]]⟩
theorem certificate3_valid : certificate3.Valid := by
  refine ⟨box3_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform3 : FamilyRationalMatrix := ![![(64743/40000 : ℚ),(-552739/1000000 : ℚ),(-346057/200000 : ℚ)],![(0/1 : ℚ),(13837/3125 : ℚ),(6119749/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(1920183/250000 : ℚ)]]
theorem margins3 : FamilyIntervalPositive (familyIntervalCongruence certificate3.hessianIntervals transform3) := by decide +kernel
theorem enclosure3 : box3.EnclosesABBOffsets offsetBox3 := by decide +kernel
theorem conclusion3 : ∀x,offsetBox3.Contains x → familyABBOffsetProperty x :=
  certificate3.abb_offset_property certificate3_valid transform3 margins3 enclosure3

def offsetBox4 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-3/32 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ)]⟩
def box4 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp40,exp4,exp8],![exp45,exp10,exp14]⟩
theorem box4_valid : box4.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp40_valid
    · exact exp4_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp45_valid
    · exact exp10_valid
    · exact exp14_valid
def certificate4 : FamilyScaledBoxCertificate := ⟨box4,![![exp40,exp21,exp24],![exp21,exp4,exp6],![exp24,exp6,exp8]],![![exp45,exp29,exp32],![exp29,exp10,exp12],![exp32,exp12,exp14]]⟩
theorem certificate4_valid : certificate4.Valid := by
  refine ⟨box4_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform4 : FamilyRationalMatrix := ![![(81019/50000 : ℚ),(-274949/500000 : ℚ),(-1721341/1000000 : ℚ)],![(0/1 : ℚ),(4427703/1000000 : ℚ),(3059663/500000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7680283/1000000 : ℚ)]]
theorem margins4 : FamilyIntervalPositive (familyIntervalCongruence certificate4.hessianIntervals transform4) := by decide +kernel
theorem enclosure4 : box4.EnclosesABBOffsets offsetBox4 := by decide +kernel
theorem conclusion4 : ∀x,offsetBox4.Contains x → familyABBOffsetProperty x :=
  certificate4.abb_offset_property certificate4_valid transform4 margins4 enclosure4

def offsetBox5 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ)],![(251/64 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ)]⟩
def box5 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp41,exp3,exp7],![exp46,exp9,exp13]⟩
theorem box5_valid : box5.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp41_valid
    · exact exp3_valid
    · exact exp7_valid
  · intro j; fin_cases j
    · exact exp46_valid
    · exact exp9_valid
    · exact exp13_valid
def certificate5 : FamilyScaledBoxCertificate := ⟨box5,![![exp41,exp22,exp25],![exp22,exp3,exp5],![exp25,exp5,exp7]],![![exp46,exp31,exp33],![exp31,exp9,exp11],![exp33,exp11,exp13]]⟩
theorem certificate5_valid : certificate5.Valid := by
  refine ⟨box5_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
def transform5 : FamilyRationalMatrix := ![![(1617121/1000000 : ℚ),(-109439/200000 : ℚ),(-847879/500000 : ℚ)],![(0/1 : ℚ),(2213623/500000 : ℚ),(6043103/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(3808563/500000 : ℚ)]]
theorem margins5 : FamilyIntervalPositive (familyIntervalCongruence certificate5.hessianIntervals transform5) := by decide +kernel
theorem enclosure5 : box5.EnclosesABBOffsets offsetBox5 := by decide +kernel
theorem conclusion5 : ∀x,offsetBox5.Contains x → familyABBOffsetProperty x :=
  certificate5.abb_offset_property certificate5_valid transform5 margins5 enclosure5

def offsetBox6 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-3/32 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ)]⟩
def box6 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp39,exp8,exp4],![exp43,exp14,exp10]⟩
theorem box6_valid : box6.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp39_valid
    · exact exp8_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp43_valid
    · exact exp14_valid
    · exact exp10_valid
def certificate6 : FamilyScaledBoxCertificate := ⟨box6,![![exp39,exp23,exp20],![exp23,exp8,exp6],![exp20,exp6,exp4]],![![exp43,exp30,exp28],![exp30,exp14,exp12],![exp28,exp12,exp10]]⟩
theorem certificate6_valid : certificate6.Valid := by
  refine ⟨box6_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp20_valid,exp28_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform6 : FamilyRationalMatrix := ![![(64743/40000 : ℚ),(-566457/1000000 : ℚ),(-1725843/1000000 : ℚ)],![(0/1 : ℚ),(900471/200000 : ℚ),(388921/62500 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(1510723/200000 : ℚ)]]
theorem margins6 : FamilyIntervalPositive (familyIntervalCongruence certificate6.hessianIntervals transform6) := by decide +kernel
theorem enclosure6 : box6.EnclosesABBOffsets offsetBox6 := by decide +kernel
theorem conclusion6 : ∀x,offsetBox6.Contains x → familyABBOffsetProperty x :=
  certificate6.abb_offset_property certificate6_valid transform6 margins6 enclosure6

def offsetBox7 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-3/32 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ)]⟩
def box7 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp40,exp8,exp4],![exp45,exp14,exp10]⟩
theorem box7_valid : box7.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp40_valid
    · exact exp8_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp45_valid
    · exact exp14_valid
    · exact exp10_valid
def certificate7 : FamilyScaledBoxCertificate := ⟨box7,![![exp40,exp24,exp21],![exp24,exp8,exp6],![exp21,exp6,exp4]],![![exp45,exp32,exp29],![exp32,exp14,exp12],![exp29,exp12,exp10]]⟩
theorem certificate7_valid : certificate7.Valid := by
  refine ⟨box7_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp21_valid,exp29_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform7 : FamilyRationalMatrix := ![![(81019/50000 : ℚ),(-563547/1000000 : ℚ),(-1716921/1000000 : ℚ)],![(0/1 : ℚ),(1125551/250000 : ℚ),(6222291/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7553191/1000000 : ℚ)]]
theorem margins7 : FamilyIntervalPositive (familyIntervalCongruence certificate7.hessianIntervals transform7) := by decide +kernel
theorem enclosure7 : box7.EnclosesABBOffsets offsetBox7 := by decide +kernel
theorem conclusion7 : ∀x,offsetBox7.Contains x → familyABBOffsetProperty x :=
  certificate7.abb_offset_property certificate7_valid transform7 margins7 enclosure7

def offsetBox8 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ)],![(251/64 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ)]⟩
def box8 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp41,exp7,exp3],![exp46,exp13,exp9]⟩
theorem box8_valid : box8.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp41_valid
    · exact exp7_valid
    · exact exp3_valid
  · intro j; fin_cases j
    · exact exp46_valid
    · exact exp13_valid
    · exact exp9_valid
def certificate8 : FamilyScaledBoxCertificate := ⟨box8,![![exp41,exp25,exp22],![exp25,exp7,exp5],![exp22,exp5,exp3]],![![exp46,exp33,exp31],![exp33,exp13,exp11],![exp31,exp11,exp9]]⟩
theorem certificate8_valid : certificate8.Valid := by
  refine ⟨box8_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp22_valid,exp31_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
def transform8 : FamilyRationalMatrix := ![![(1617121/1000000 : ℚ),(-112151/200000 : ℚ),(-1691323/1000000 : ℚ)],![(0/1 : ℚ),(2250803/500000 : ℚ),(6144603/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(3745651/500000 : ℚ)]]
theorem margins8 : FamilyIntervalPositive (familyIntervalCongruence certificate8.hessianIntervals transform8) := by decide +kernel
theorem enclosure8 : box8.EnclosesABBOffsets offsetBox8 := by decide +kernel
theorem conclusion8 : ∀x,offsetBox8.Contains x → familyABBOffsetProperty x :=
  certificate8.abb_offset_property certificate8_valid transform8 margins8 enclosure8

def offsetBox9 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-3/32 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def box9 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp39,exp8,exp8],![exp43,exp14,exp14]⟩
theorem box9_valid : box9.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp39_valid
    · exact exp8_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp43_valid
    · exact exp14_valid
    · exact exp14_valid
def certificate9 : FamilyScaledBoxCertificate := ⟨box9,![![exp39,exp23,exp23],![exp23,exp8,exp8],![exp23,exp8,exp8]],![![exp43,exp30,exp30],![exp30,exp14,exp14],![exp30,exp14,exp14]]⟩
theorem certificate9_valid : certificate9.Valid := by
  refine ⟨box9_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp30_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
def transform9 : FamilyRationalMatrix := ![![(1633533/1000000 : ℚ),(-561077/1000000 : ℚ),(-216179/125000 : ℚ)],![(0/1 : ℚ),(559767/125000 : ℚ),(1543791/250000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7627997/1000000 : ℚ)]]
theorem margins9 : FamilyIntervalPositive (familyIntervalCongruence certificate9.hessianIntervals transform9) := by decide +kernel
theorem enclosure9 : box9.EnclosesABBOffsets offsetBox9 := by decide +kernel
theorem conclusion9 : ∀x,offsetBox9.Contains x → familyABBOffsetProperty x :=
  certificate9.abb_offset_property certificate9_valid transform9 margins9 enclosure9

def offsetBox10 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-3/32 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def box10 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp40,exp8,exp8],![exp45,exp14,exp14]⟩
theorem box10_valid : box10.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp40_valid
    · exact exp8_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp45_valid
    · exact exp14_valid
    · exact exp14_valid
def certificate10 : FamilyScaledBoxCertificate := ⟨box10,![![exp40,exp24,exp24],![exp24,exp8,exp8],![exp24,exp8,exp8]],![![exp45,exp32,exp32],![exp32,exp14,exp14],![exp32,exp14,exp14]]⟩
theorem certificate10_valid : certificate10.Valid := by
  refine ⟨box10_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp24_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
def transform10 : FamilyRationalMatrix := ![![(32707/20000 : ℚ),(-558169/1000000 : ℚ),(-430107/250000 : ℚ)],![(0/1 : ℚ),(2238997/500000 : ℚ),(6174787/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7627609/1000000 : ℚ)]]
theorem margins10 : FamilyIntervalPositive (familyIntervalCongruence certificate10.hessianIntervals transform10) := by decide +kernel
theorem enclosure10 : box10.EnclosesABBOffsets offsetBox10 := by decide +kernel
theorem conclusion10 : ∀x,offsetBox10.Contains x → familyABBOffsetProperty x :=
  certificate10.abb_offset_property certificate10_valid transform10 margins10 enclosure10

def offsetBox11 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)],![(251/64 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def box11 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp41,exp7,exp7],![exp46,exp13,exp13]⟩
theorem box11_valid : box11.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp41_valid
    · exact exp7_valid
    · exact exp7_valid
  · intro j; fin_cases j
    · exact exp46_valid
    · exact exp13_valid
    · exact exp13_valid
def certificate11 : FamilyScaledBoxCertificate := ⟨box11,![![exp41,exp25,exp25],![exp25,exp7,exp7],![exp25,exp7,exp7]],![![exp46,exp33,exp33],![exp33,exp13,exp13],![exp33,exp13,exp13]]⟩
theorem certificate11_valid : certificate11.Valid := by
  refine ⟨box11_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp7_valid,exp13_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp7_valid,exp13_valid,by decide +kernel,by decide +kernel⟩
def transform11 : FamilyRationalMatrix := ![![(1632037/1000000 : ℚ),(-555413/1000000 : ℚ),(-847479/500000 : ℚ)],![(0/1 : ℚ),(1119377/250000 : ℚ),(6098417/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7565631/1000000 : ℚ)]]
theorem margins11 : FamilyIntervalPositive (familyIntervalCongruence certificate11.hessianIntervals transform11) := by decide +kernel
theorem enclosure11 : box11.EnclosesABBOffsets offsetBox11 := by decide +kernel
theorem conclusion11 : ∀x,offsetBox11.Contains x → familyABBOffsetProperty x :=
  certificate11.abb_offset_property certificate11_valid transform11 margins11 enclosure11

def offsetBox12 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)]⟩
def box12 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp42,exp4,exp4],![exp47,exp10,exp10]⟩
theorem box12_valid : box12.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp42_valid
    · exact exp4_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp47_valid
    · exact exp10_valid
    · exact exp10_valid
def certificate12 : FamilyScaledBoxCertificate := ⟨box12,![![exp42,exp23,exp23],![exp23,exp4,exp4],![exp23,exp4,exp4]],![![exp47,exp32,exp32],![exp32,exp10,exp10],![exp32,exp10,exp10]]⟩
theorem certificate12_valid : certificate12.Valid := by
  refine ⟨box12_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp4_valid,exp10_valid,by decide +kernel,by decide +kernel⟩
def transform12 : FamilyRationalMatrix := ![![(1608219/1000000 : ℚ),(-275441/500000 : ℚ),(-425799/250000 : ℚ)],![(0/1 : ℚ),(1112721/250000 : ℚ),(770093/125000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7600337/1000000 : ℚ)]]
theorem margins12 : FamilyIntervalPositive (familyIntervalCongruence certificate12.hessianIntervals transform12) := by decide +kernel
theorem enclosure12 : box12.EnclosesABBOffsets offsetBox12 := by decide +kernel
theorem conclusion12 : ∀x,offsetBox12.Contains x → familyABBOffsetProperty x :=
  certificate12.abb_offset_property certificate12_valid transform12 margins12 enclosure12

def offsetBox13 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ),(-1/10 : ℚ)],![(251/64 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)]⟩
def box13 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp44,exp3,exp3],![exp48,exp9,exp9]⟩
theorem box13_valid : box13.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp44_valid
    · exact exp3_valid
    · exact exp3_valid
  · intro j; fin_cases j
    · exact exp48_valid
    · exact exp9_valid
    · exact exp9_valid
def certificate13 : FamilyScaledBoxCertificate := ⟨box13,![![exp44,exp25,exp25],![exp25,exp3,exp3],![exp25,exp3,exp3]],![![exp48,exp33,exp33],![exp33,exp9,exp9],![exp33,exp9,exp9]]⟩
theorem certificate13_valid : certificate13.Valid := by
  refine ⟨box13_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp3_valid,exp9_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp3_valid,exp9_valid,by decide +kernel,by decide +kernel⟩
def transform13 : FamilyRationalMatrix := ![![(1605913/1000000 : ℚ),(-273351/500000 : ℚ),(-836621/500000 : ℚ)],![(0/1 : ℚ),(2225133/500000 : ℚ),(24333/4000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7537293/1000000 : ℚ)]]
theorem margins13 : FamilyIntervalPositive (familyIntervalCongruence certificate13.hessianIntervals transform13) := by decide +kernel
theorem enclosure13 : box13.EnclosesABBOffsets offsetBox13 := by decide +kernel
theorem conclusion13 : ∀x,offsetBox13.Contains x → familyABBOffsetProperty x :=
  certificate13.abb_offset_property certificate13_valid transform13 margins13 enclosure13

def offsetBox14 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ)]⟩
def box14 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp42,exp4,exp8],![exp47,exp10,exp14]⟩
theorem box14_valid : box14.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp42_valid
    · exact exp4_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp47_valid
    · exact exp10_valid
    · exact exp14_valid
def certificate14 : FamilyScaledBoxCertificate := ⟨box14,![![exp42,exp23,exp26],![exp23,exp4,exp6],![exp26,exp6,exp8]],![![exp47,exp32,exp34],![exp32,exp10,exp12],![exp34,exp12,exp14]]⟩
theorem certificate14_valid : certificate14.Valid := by
  refine ⟨box14_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform14 : FamilyRationalMatrix := ![![(50721/31250 : ℚ),(-5457/10000 : ℚ),(-1708163/1000000 : ℚ)],![(0/1 : ℚ),(885499/200000 : ℚ),(95607/15625 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(3839869/500000 : ℚ)]]
theorem margins14 : FamilyIntervalPositive (familyIntervalCongruence certificate14.hessianIntervals transform14) := by decide +kernel
theorem enclosure14 : box14.EnclosesABBOffsets offsetBox14 := by decide +kernel
theorem conclusion14 : ∀x,offsetBox14.Contains x → familyABBOffsetProperty x :=
  certificate14.abb_offset_property certificate14_valid transform14 margins14 enclosure14

def offsetBox15 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ),(-7/80 : ℚ)],![(251/64 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ),(-3/40 : ℚ)]⟩
def box15 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp44,exp3,exp7],![exp48,exp9,exp13]⟩
theorem box15_valid : box15.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp44_valid
    · exact exp3_valid
    · exact exp7_valid
  · intro j; fin_cases j
    · exact exp48_valid
    · exact exp9_valid
    · exact exp13_valid
def certificate15 : FamilyScaledBoxCertificate := ⟨box15,![![exp44,exp25,exp27],![exp25,exp3,exp5],![exp27,exp5,exp7]],![![exp48,exp33,exp35],![exp33,exp9,exp11],![exp35,exp11,exp13]]⟩
theorem certificate15_valid : certificate15.Valid := by
  refine ⟨box15_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
def transform15 : FamilyRationalMatrix := ![![(1620719/1000000 : ℚ),(-135389/250000 : ℚ),(-1678243/1000000 : ℚ)],![(0/1 : ℚ),(4426989/1000000 : ℚ),(6042539/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(304659/40000 : ℚ)]]
theorem margins15 : FamilyIntervalPositive (familyIntervalCongruence certificate15.hessianIntervals transform15) := by decide +kernel
theorem enclosure15 : box15.EnclosesABBOffsets offsetBox15 := by decide +kernel
theorem conclusion15 : ∀x,offsetBox15.Contains x → familyABBOffsetProperty x :=
  certificate15.abb_offset_property certificate15_valid transform15 margins15 enclosure15

def offsetBox16 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ)],![(2503/640 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ)]⟩
def box16 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp42,exp8,exp4],![exp47,exp14,exp10]⟩
theorem box16_valid : box16.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp42_valid
    · exact exp8_valid
    · exact exp4_valid
  · intro j; fin_cases j
    · exact exp47_valid
    · exact exp14_valid
    · exact exp10_valid
def certificate16 : FamilyScaledBoxCertificate := ⟨box16,![![exp42,exp26,exp23],![exp26,exp8,exp6],![exp23,exp6,exp4]],![![exp47,exp34,exp32],![exp34,exp14,exp12],![exp32,exp12,exp10]]⟩
theorem certificate16_valid : certificate16.Valid := by
  refine ⟨box16_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp23_valid,exp32_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp6_valid,exp12_valid,by decide +kernel,by decide +kernel⟩
def transform16 : FamilyRationalMatrix := ![![(50721/31250 : ℚ),(-559249/1000000 : ℚ),(-68151/40000 : ℚ)],![(0/1 : ℚ),(4501977/1000000 : ℚ),(6221783/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(3776341/500000 : ℚ)]]
theorem margins16 : FamilyIntervalPositive (familyIntervalCongruence certificate16.hessianIntervals transform16) := by decide +kernel
theorem enclosure16 : box16.EnclosesABBOffsets offsetBox16 := by decide +kernel
theorem conclusion16 : ∀x,offsetBox16.Contains x → familyABBOffsetProperty x :=
  certificate16.abb_offset_property certificate16_valid transform16 margins16 enclosure16

def offsetBox17 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-1/10 : ℚ)],![(251/64 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ),(-7/80 : ℚ)]⟩
def box17 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp44,exp7,exp3],![exp48,exp13,exp9]⟩
theorem box17_valid : box17.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp44_valid
    · exact exp7_valid
    · exact exp3_valid
  · intro j; fin_cases j
    · exact exp48_valid
    · exact exp13_valid
    · exact exp9_valid
def certificate17 : FamilyScaledBoxCertificate := ⟨box17,![![exp44,exp27,exp25],![exp27,exp7,exp5],![exp25,exp5,exp3]],![![exp48,exp35,exp33],![exp35,exp13,exp11],![exp33,exp11,exp9]]⟩
theorem certificate17_valid : certificate17.Valid := by
  refine ⟨box17_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp25_valid,exp33_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp5_valid,exp11_valid,by decide +kernel,by decide +kernel⟩
def transform17 : FamilyRationalMatrix := ![![(1620719/1000000 : ℚ),(-554981/1000000 : ℚ),(-1673851/1000000 : ℚ)],![(0/1 : ℚ),(180053/40000 : ℚ),(6144003/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(1498139/200000 : ℚ)]]
theorem margins17 : FamilyIntervalPositive (familyIntervalCongruence certificate17.hessianIntervals transform17) := by decide +kernel
theorem enclosure17 : box17.EnclosesABBOffsets offsetBox17 := by decide +kernel
theorem conclusion17 : ∀x,offsetBox17.Contains x → familyABBOffsetProperty x :=
  certificate17.abb_offset_property certificate17_valid transform17 margins17 enclosure17

def offsetBox18 : ReplayBox 4 := ⟨![(39/10 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)],![(2503/640 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def box18 : FamilyBoxCertificate := ⟨parameter0,coefficients0,![exp42,exp8,exp8],![exp47,exp14,exp14]⟩
theorem box18_valid : box18.Valid := by
  refine ⟨parameter0_valid,coefficients0_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp42_valid
    · exact exp8_valid
    · exact exp8_valid
  · intro j; fin_cases j
    · exact exp47_valid
    · exact exp14_valid
    · exact exp14_valid
def certificate18 : FamilyScaledBoxCertificate := ⟨box18,![![exp42,exp26,exp26],![exp26,exp8,exp8],![exp26,exp8,exp8]],![![exp47,exp34,exp34],![exp34,exp14,exp14],![exp34,exp14,exp14]]⟩
theorem certificate18_valid : certificate18.Valid := by
  refine ⟨box18_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp26_valid,exp34_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp8_valid,exp14_valid,by decide +kernel,by decide +kernel⟩
def transform18 : FamilyRationalMatrix := ![![(1638059/1000000 : ℚ),(-34617/62500 : ℚ),(-1707159/1000000 : ℚ)],![(0/1 : ℚ),(4477779/1000000 : ℚ),(6174377/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7627151/1000000 : ℚ)]]
theorem margins18 : FamilyIntervalPositive (familyIntervalCongruence certificate18.hessianIntervals transform18) := by decide +kernel
theorem enclosure18 : box18.EnclosesABBOffsets offsetBox18 := by decide +kernel
theorem conclusion18 : ∀x,offsetBox18.Contains x → familyABBOffsetProperty x :=
  certificate18.abb_offset_property certificate18_valid transform18 margins18 enclosure18

def offsetBox19 : ReplayBox 4 := ⟨![(2503/640 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ),(-7/80 : ℚ)],![(251/64 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ),(-3/40 : ℚ)]⟩
def box19 : FamilyBoxCertificate := ⟨parameter1,coefficients1,![exp44,exp7,exp7],![exp48,exp13,exp13]⟩
theorem box19_valid : box19.Valid := by
  refine ⟨parameter1_valid,coefficients1_checked,?_,?_⟩
  · intro j; fin_cases j
    · exact exp44_valid
    · exact exp7_valid
    · exact exp7_valid
  · intro j; fin_cases j
    · exact exp48_valid
    · exact exp13_valid
    · exact exp13_valid
def certificate19 : FamilyScaledBoxCertificate := ⟨box19,![![exp44,exp27,exp27],![exp27,exp7,exp7],![exp27,exp7,exp7]],![![exp48,exp35,exp35],![exp35,exp13,exp13],![exp35,exp13,exp13]]⟩
theorem certificate19_valid : certificate19.Valid := by
  refine ⟨box19_valid,?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp7_valid,exp13_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp27_valid,exp35_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨exp7_valid,exp13_valid,by decide +kernel,by decide +kernel⟩
def transform19 : FamilyRationalMatrix := ![![(1635659/1000000 : ℚ),(-274821/500000 : ℚ),(-1677323/1000000 : ℚ)],![(0/1 : ℚ),(4477243/1000000 : ℚ),(6097949/1000000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7565097/1000000 : ℚ)]]
theorem margins19 : FamilyIntervalPositive (familyIntervalCongruence certificate19.hessianIntervals transform19) := by decide +kernel
theorem enclosure19 : box19.EnclosesABBOffsets offsetBox19 := by decide +kernel
theorem conclusion19 : ∀x,offsetBox19.Contains x → familyABBOffsetProperty x :=
  certificate19.abb_offset_property certificate19_valid transform19 margins19 enclosure19

end SparseLowerTail.Section08.FamilyABBReplay.Smoke
