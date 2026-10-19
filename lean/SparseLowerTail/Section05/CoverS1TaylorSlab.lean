import SparseLowerTail.Section05.CoverS1CachedTaylor
import SparseLowerTail.Section05.CoverTreeReplay

/-! Seventeen actual Taylor leaves cover an entire substantial rectangular slab.
Every exponential bracket, integer margin, and subdivision identity is checked
by Lean's kernel. No numerical proposal status is accepted as evidence. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000


def s1SlabExp0 : ExpEndpointCertificate :=
  ⟨(20229/4096 : ℚ),20,(423366068169979813/576460752303423488 : ℚ),(846732136339959627/1152921504606846976 : ℚ),(2064812399200203/288230376151711744 : ℚ),(8259249596800813/1152921504606846976 : ℚ)⟩

theorem s1SlabExp0_valid : s1SlabExp0.Valid := by decide +kernel

def s1SlabExp1 : ExpEndpointCertificate :=
  ⟨(87659/16384 : ℚ),20,(206307449603057809/288230376151711744 : ℚ),(825229798412231237/1152921504606846976 : ℚ),(2736354325767789/576460752303423488 : ℚ),(5472708651535579/1152921504606846976 : ℚ)⟩

theorem s1SlabExp1_valid : s1SlabExp1.Valid := by decide +kernel

def s1SlabExp2 : ExpEndpointCertificate :=
  ⟨(47201/8192 : ℚ),20,(201068375392944601/288230376151711744 : ℚ),(804273501571778405/1152921504606846976 : ℚ),(3626302805547079/1152921504606846976 : ℚ),(453287850693385/144115188075855872 : ℚ)⟩

theorem s1SlabExp2_valid : s1SlabExp2.Valid := by decide +kernel

def s1SlabExp3 : ExpEndpointCertificate :=
  ⟨(101145/16384 : ℚ),20,(195962344844763543/288230376151711744 : ℚ),(783849379379054173/1152921504606846976 : ℚ),(2402845259052637/1152921504606846976 : ℚ),(1201422629526319/576460752303423488 : ℚ)⟩

theorem s1SlabExp3_valid : s1SlabExp3.Valid := by decide +kernel

def s1SlabExp4 : ExpEndpointCertificate :=
  ⟨(6743/1024 : ℚ),20,(381971958762894615/576460752303423488 : ℚ),(763943917525789231/1152921504606846976 : ℚ),(796081525530615/576460752303423488 : ℚ),(1592163051061231/1152921504606846976 : ℚ)⟩

theorem s1SlabExp4_valid : s1SlabExp4.Valid := by decide +kernel

def s1SlabExp5 : ExpEndpointCertificate :=
  ⟨(60687/8192 : ℚ),20,(181409156208711925/288230376151711744 : ℚ),(725636624834847701/1152921504606846976 : ℚ),(699054468724149/1152921504606846976 : ℚ),(349527234362075/576460752303423488 : ℚ)⟩

theorem s1SlabExp5_valid : s1SlabExp5.Valid := by decide +kernel

def s1SlabExp6 : ExpEndpointCertificate :=
  ⟨(33715/4096 : ℚ),20,(689250217485937739/1152921504606846976 : ℚ),(172312554371484435/288230376151711744 : ℚ),(306926573831419/1152921504606846976 : ℚ),(76731643457855/288230376151711744 : ℚ)⟩

theorem s1SlabExp6_valid : s1SlabExp6.Valid := by decide +kernel

def s1SlabExp7 : ExpEndpointCertificate :=
  ⟨(74173/8192 : ℚ),20,(327344187190479645/576460752303423488 : ℚ),(654688374380959291/1152921504606846976 : ℚ),(134759058039963/1152921504606846976 : ℚ),(33689764509991/288230376151711744 : ℚ)⟩

theorem s1SlabExp7_valid : s1SlabExp7.Valid := by decide +kernel

def s1SlabExp8 : ExpEndpointCertificate :=
  ⟨(20229/2048 : ℚ),20,(621859604358163101/1152921504606846976 : ℚ),(310929802179081551/576460752303423488 : ℚ),(14791814453473/288230376151711744 : ℚ),(59167257813893/1152921504606846976 : ℚ)⟩

theorem s1SlabExp8_valid : s1SlabExp8.Valid := by decide +kernel

def s1SlabExp9 : ExpEndpointCertificate :=
  ⟨(87659/8192 : ℚ),20,(73834625499907543/144115188075855872 : ℚ),(590677003999260345/1152921504606846976 : ℚ),(25977952414727/1152921504606846976 : ℚ),(3247244051841/144115188075855872 : ℚ)⟩

theorem s1SlabExp9_valid : s1SlabExp9.Valid := by decide +kernel

def s1SlabExp10 : ExpEndpointCertificate :=
  ⟨(47201/4096 : ℚ),20,(561058027581080725/1152921504606846976 : ℚ),(280529013790540363/576460752303423488 : ℚ),(5702934668567/576460752303423488 : ℚ),(11405869337135/1152921504606846976 : ℚ)⟩

theorem s1SlabExp10_valid : s1SlabExp10.Valid := by decide +kernel

def s1SlabExp11 : ExpEndpointCertificate :=
  ⟨(101145/8192 : ℚ),20,(266462134281400703/576460752303423488 : ℚ),(532924268562801407/1152921504606846976 : ℚ),(1251964100739/288230376151711744 : ℚ),(5007856402957/1152921504606846976 : ℚ)⟩

theorem s1SlabExp11_valid : s1SlabExp11.Valid := by decide +kernel

def s1SlabExp12 : ExpEndpointCertificate :=
  ⟨(6743/512 : ℚ),20,(253100626015152875/576460752303423488 : ℚ),(506201252030305751/1152921504606846976 : ℚ),(1099373708893/576460752303423488 : ℚ),(2198747417787/1152921504606846976 : ℚ)⟩

theorem s1SlabExp12_valid : s1SlabExp12.Valid := by decide +kernel

def s1SlabBox0 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox1 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox2 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox3 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox4 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(33715/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox5 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(33715/4096 : ℚ),(47201/8192 : ℚ)]⟩

def s1SlabData5 : S1TaylorBoxData :=
  ⟨s1SlabBox5,![s1SlabExp4,s1SlabExp4,s1SlabExp0],![s1SlabExp6,s1SlabExp6,s1SlabExp2],![s1SlabExp5,s1SlabExp5,s1SlabExp1]⟩

theorem s1SlabData5_lower_valid : ∀ i, (s1SlabData5.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp4_valid
  · exact s1SlabExp4_valid
  · exact s1SlabExp0_valid


theorem s1SlabData5_upper_valid : ∀ i, (s1SlabData5.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp2_valid


theorem s1SlabData5_center_valid : ∀ i, (s1SlabData5.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp5_valid
  · exact s1SlabExp5_valid
  · exact s1SlabExp1_valid


theorem s1SlabData5_margin : 0 < s1SlabData5.cachedDyadicMargin := by decide +kernel

def s1SlabBox6 : LogBox := ⟨![(6743/1024 : ℚ),(6743/1024 : ℚ),(47201/8192 : ℚ)],![(33715/4096 : ℚ),(33715/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData6 : S1TaylorBoxData :=
  ⟨s1SlabBox6,![s1SlabExp4,s1SlabExp4,s1SlabExp2],![s1SlabExp6,s1SlabExp6,s1SlabExp4],![s1SlabExp5,s1SlabExp5,s1SlabExp3]⟩

theorem s1SlabData6_lower_valid : ∀ i, (s1SlabData6.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp4_valid
  · exact s1SlabExp4_valid
  · exact s1SlabExp2_valid


theorem s1SlabData6_upper_valid : ∀ i, (s1SlabData6.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp4_valid


theorem s1SlabData6_center_valid : ∀ i, (s1SlabData6.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp5_valid
  · exact s1SlabExp5_valid
  · exact s1SlabExp3_valid


theorem s1SlabData6_margin : 0 < s1SlabData6.cachedDyadicMargin := by decide +kernel

def s1SlabBox7 : LogBox := ⟨![(6743/1024 : ℚ),(33715/4096 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData7 : S1TaylorBoxData :=
  ⟨s1SlabBox7,![s1SlabExp4,s1SlabExp6,s1SlabExp0],![s1SlabExp6,s1SlabExp8,s1SlabExp4],![s1SlabExp5,s1SlabExp7,s1SlabExp2]⟩

theorem s1SlabData7_lower_valid : ∀ i, (s1SlabData7.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp4_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp0_valid


theorem s1SlabData7_upper_valid : ∀ i, (s1SlabData7.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp4_valid


theorem s1SlabData7_center_valid : ∀ i, (s1SlabData7.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp5_valid
  · exact s1SlabExp7_valid
  · exact s1SlabExp2_valid


theorem s1SlabData7_margin : 0 < s1SlabData7.cachedDyadicMargin := by decide +kernel

def s1SlabBox8 : LogBox := ⟨![(6743/1024 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox9 : LogBox := ⟨![(6743/1024 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(47201/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData9 : S1TaylorBoxData :=
  ⟨s1SlabBox9,![s1SlabExp4,s1SlabExp8,s1SlabExp0],![s1SlabExp6,s1SlabExp10,s1SlabExp4],![s1SlabExp5,s1SlabExp9,s1SlabExp2]⟩

theorem s1SlabData9_lower_valid : ∀ i, (s1SlabData9.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp4_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp0_valid


theorem s1SlabData9_upper_valid : ∀ i, (s1SlabData9.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp4_valid


theorem s1SlabData9_center_valid : ∀ i, (s1SlabData9.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp5_valid
  · exact s1SlabExp9_valid
  · exact s1SlabExp2_valid


theorem s1SlabData9_margin : 0 < s1SlabData9.cachedDyadicMargin := by decide +kernel

def s1SlabBox10 : LogBox := ⟨![(6743/1024 : ℚ),(47201/4096 : ℚ),(20229/4096 : ℚ)],![(33715/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData10 : S1TaylorBoxData :=
  ⟨s1SlabBox10,![s1SlabExp4,s1SlabExp10,s1SlabExp0],![s1SlabExp6,s1SlabExp12,s1SlabExp4],![s1SlabExp5,s1SlabExp11,s1SlabExp2]⟩

theorem s1SlabData10_lower_valid : ∀ i, (s1SlabData10.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp4_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp0_valid


theorem s1SlabData10_upper_valid : ∀ i, (s1SlabData10.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp12_valid
  · exact s1SlabExp4_valid


theorem s1SlabData10_center_valid : ∀ i, (s1SlabData10.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp5_valid
  · exact s1SlabExp11_valid
  · exact s1SlabExp2_valid


theorem s1SlabData10_margin : 0 < s1SlabData10.cachedDyadicMargin := by decide +kernel

def s1SlabBox11 : LogBox := ⟨![(33715/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox12 : LogBox := ⟨![(33715/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox13 : LogBox := ⟨![(33715/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(33715/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData13 : S1TaylorBoxData :=
  ⟨s1SlabBox13,![s1SlabExp6,s1SlabExp4,s1SlabExp0],![s1SlabExp8,s1SlabExp6,s1SlabExp4],![s1SlabExp7,s1SlabExp5,s1SlabExp2]⟩

theorem s1SlabData13_lower_valid : ∀ i, (s1SlabData13.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp4_valid
  · exact s1SlabExp0_valid


theorem s1SlabData13_upper_valid : ∀ i, (s1SlabData13.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp4_valid


theorem s1SlabData13_center_valid : ∀ i, (s1SlabData13.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp7_valid
  · exact s1SlabExp5_valid
  · exact s1SlabExp2_valid


theorem s1SlabData13_margin : 0 < s1SlabData13.cachedDyadicMargin := by decide +kernel

def s1SlabBox14 : LogBox := ⟨![(33715/4096 : ℚ),(33715/4096 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData14 : S1TaylorBoxData :=
  ⟨s1SlabBox14,![s1SlabExp6,s1SlabExp6,s1SlabExp0],![s1SlabExp8,s1SlabExp8,s1SlabExp4],![s1SlabExp7,s1SlabExp7,s1SlabExp2]⟩

theorem s1SlabData14_lower_valid : ∀ i, (s1SlabData14.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp0_valid


theorem s1SlabData14_upper_valid : ∀ i, (s1SlabData14.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp4_valid


theorem s1SlabData14_center_valid : ∀ i, (s1SlabData14.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp7_valid
  · exact s1SlabExp7_valid
  · exact s1SlabExp2_valid


theorem s1SlabData14_margin : 0 < s1SlabData14.cachedDyadicMargin := by decide +kernel

def s1SlabBox15 : LogBox := ⟨![(33715/4096 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox16 : LogBox := ⟨![(33715/4096 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(47201/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData16 : S1TaylorBoxData :=
  ⟨s1SlabBox16,![s1SlabExp6,s1SlabExp8,s1SlabExp0],![s1SlabExp8,s1SlabExp10,s1SlabExp4],![s1SlabExp7,s1SlabExp9,s1SlabExp2]⟩

theorem s1SlabData16_lower_valid : ∀ i, (s1SlabData16.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp0_valid


theorem s1SlabData16_upper_valid : ∀ i, (s1SlabData16.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp4_valid


theorem s1SlabData16_center_valid : ∀ i, (s1SlabData16.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp7_valid
  · exact s1SlabExp9_valid
  · exact s1SlabExp2_valid


theorem s1SlabData16_margin : 0 < s1SlabData16.cachedDyadicMargin := by decide +kernel

def s1SlabBox17 : LogBox := ⟨![(33715/4096 : ℚ),(47201/4096 : ℚ),(20229/4096 : ℚ)],![(20229/2048 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData17 : S1TaylorBoxData :=
  ⟨s1SlabBox17,![s1SlabExp6,s1SlabExp10,s1SlabExp0],![s1SlabExp8,s1SlabExp12,s1SlabExp4],![s1SlabExp7,s1SlabExp11,s1SlabExp2]⟩

theorem s1SlabData17_lower_valid : ∀ i, (s1SlabData17.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp6_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp0_valid


theorem s1SlabData17_upper_valid : ∀ i, (s1SlabData17.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp12_valid
  · exact s1SlabExp4_valid


theorem s1SlabData17_center_valid : ∀ i, (s1SlabData17.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp7_valid
  · exact s1SlabExp11_valid
  · exact s1SlabExp2_valid


theorem s1SlabData17_margin : 0 < s1SlabData17.cachedDyadicMargin := by decide +kernel

def s1SlabBox18 : LogBox := ⟨![(20229/2048 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox19 : LogBox := ⟨![(20229/2048 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox20 : LogBox := ⟨![(20229/2048 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox21 : LogBox := ⟨![(20229/2048 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(33715/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData21 : S1TaylorBoxData :=
  ⟨s1SlabBox21,![s1SlabExp8,s1SlabExp4,s1SlabExp0],![s1SlabExp10,s1SlabExp6,s1SlabExp4],![s1SlabExp9,s1SlabExp5,s1SlabExp2]⟩

theorem s1SlabData21_lower_valid : ∀ i, (s1SlabData21.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp4_valid
  · exact s1SlabExp0_valid


theorem s1SlabData21_upper_valid : ∀ i, (s1SlabData21.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp4_valid


theorem s1SlabData21_center_valid : ∀ i, (s1SlabData21.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp9_valid
  · exact s1SlabExp5_valid
  · exact s1SlabExp2_valid


theorem s1SlabData21_margin : 0 < s1SlabData21.cachedDyadicMargin := by decide +kernel

def s1SlabBox22 : LogBox := ⟨![(20229/2048 : ℚ),(33715/4096 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData22 : S1TaylorBoxData :=
  ⟨s1SlabBox22,![s1SlabExp8,s1SlabExp6,s1SlabExp0],![s1SlabExp10,s1SlabExp8,s1SlabExp4],![s1SlabExp9,s1SlabExp7,s1SlabExp2]⟩

theorem s1SlabData22_lower_valid : ∀ i, (s1SlabData22.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp0_valid


theorem s1SlabData22_upper_valid : ∀ i, (s1SlabData22.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp4_valid


theorem s1SlabData22_center_valid : ∀ i, (s1SlabData22.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp9_valid
  · exact s1SlabExp7_valid
  · exact s1SlabExp2_valid


theorem s1SlabData22_margin : 0 < s1SlabData22.cachedDyadicMargin := by decide +kernel

def s1SlabBox23 : LogBox := ⟨![(20229/2048 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox24 : LogBox := ⟨![(20229/2048 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(47201/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData24 : S1TaylorBoxData :=
  ⟨s1SlabBox24,![s1SlabExp8,s1SlabExp8,s1SlabExp0],![s1SlabExp10,s1SlabExp10,s1SlabExp4],![s1SlabExp9,s1SlabExp9,s1SlabExp2]⟩

theorem s1SlabData24_lower_valid : ∀ i, (s1SlabData24.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp0_valid


theorem s1SlabData24_upper_valid : ∀ i, (s1SlabData24.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp4_valid


theorem s1SlabData24_center_valid : ∀ i, (s1SlabData24.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp9_valid
  · exact s1SlabExp9_valid
  · exact s1SlabExp2_valid


theorem s1SlabData24_margin : 0 < s1SlabData24.cachedDyadicMargin := by decide +kernel

def s1SlabBox25 : LogBox := ⟨![(20229/2048 : ℚ),(47201/4096 : ℚ),(20229/4096 : ℚ)],![(47201/4096 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData25 : S1TaylorBoxData :=
  ⟨s1SlabBox25,![s1SlabExp8,s1SlabExp10,s1SlabExp0],![s1SlabExp10,s1SlabExp12,s1SlabExp4],![s1SlabExp9,s1SlabExp11,s1SlabExp2]⟩

theorem s1SlabData25_lower_valid : ∀ i, (s1SlabData25.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp8_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp0_valid


theorem s1SlabData25_upper_valid : ∀ i, (s1SlabData25.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp12_valid
  · exact s1SlabExp4_valid


theorem s1SlabData25_center_valid : ∀ i, (s1SlabData25.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp9_valid
  · exact s1SlabExp11_valid
  · exact s1SlabExp2_valid


theorem s1SlabData25_margin : 0 < s1SlabData25.cachedDyadicMargin := by decide +kernel

def s1SlabBox26 : LogBox := ⟨![(47201/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox27 : LogBox := ⟨![(47201/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox28 : LogBox := ⟨![(47201/4096 : ℚ),(6743/1024 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(33715/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData28 : S1TaylorBoxData :=
  ⟨s1SlabBox28,![s1SlabExp10,s1SlabExp4,s1SlabExp0],![s1SlabExp12,s1SlabExp6,s1SlabExp4],![s1SlabExp11,s1SlabExp5,s1SlabExp2]⟩

theorem s1SlabData28_lower_valid : ∀ i, (s1SlabData28.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp4_valid
  · exact s1SlabExp0_valid


theorem s1SlabData28_upper_valid : ∀ i, (s1SlabData28.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp12_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp4_valid


theorem s1SlabData28_center_valid : ∀ i, (s1SlabData28.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp11_valid
  · exact s1SlabExp5_valid
  · exact s1SlabExp2_valid


theorem s1SlabData28_margin : 0 < s1SlabData28.cachedDyadicMargin := by decide +kernel

def s1SlabBox29 : LogBox := ⟨![(47201/4096 : ℚ),(33715/4096 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(20229/2048 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData29 : S1TaylorBoxData :=
  ⟨s1SlabBox29,![s1SlabExp10,s1SlabExp6,s1SlabExp0],![s1SlabExp12,s1SlabExp8,s1SlabExp4],![s1SlabExp11,s1SlabExp7,s1SlabExp2]⟩

theorem s1SlabData29_lower_valid : ∀ i, (s1SlabData29.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp6_valid
  · exact s1SlabExp0_valid


theorem s1SlabData29_upper_valid : ∀ i, (s1SlabData29.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp12_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp4_valid


theorem s1SlabData29_center_valid : ∀ i, (s1SlabData29.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp11_valid
  · exact s1SlabExp7_valid
  · exact s1SlabExp2_valid


theorem s1SlabData29_margin : 0 < s1SlabData29.cachedDyadicMargin := by decide +kernel

def s1SlabBox30 : LogBox := ⟨![(47201/4096 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabBox31 : LogBox := ⟨![(47201/4096 : ℚ),(20229/2048 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(47201/4096 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData31 : S1TaylorBoxData :=
  ⟨s1SlabBox31,![s1SlabExp10,s1SlabExp8,s1SlabExp0],![s1SlabExp12,s1SlabExp10,s1SlabExp4],![s1SlabExp11,s1SlabExp9,s1SlabExp2]⟩

theorem s1SlabData31_lower_valid : ∀ i, (s1SlabData31.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp8_valid
  · exact s1SlabExp0_valid


theorem s1SlabData31_upper_valid : ∀ i, (s1SlabData31.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp12_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp4_valid


theorem s1SlabData31_center_valid : ∀ i, (s1SlabData31.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp11_valid
  · exact s1SlabExp9_valid
  · exact s1SlabExp2_valid


theorem s1SlabData31_margin : 0 < s1SlabData31.cachedDyadicMargin := by decide +kernel

def s1SlabBox32 : LogBox := ⟨![(47201/4096 : ℚ),(47201/4096 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1SlabData32 : S1TaylorBoxData :=
  ⟨s1SlabBox32,![s1SlabExp10,s1SlabExp10,s1SlabExp0],![s1SlabExp12,s1SlabExp12,s1SlabExp4],![s1SlabExp11,s1SlabExp11,s1SlabExp2]⟩

theorem s1SlabData32_lower_valid : ∀ i, (s1SlabData32.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp10_valid
  · exact s1SlabExp10_valid
  · exact s1SlabExp0_valid


theorem s1SlabData32_upper_valid : ∀ i, (s1SlabData32.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp12_valid
  · exact s1SlabExp12_valid
  · exact s1SlabExp4_valid


theorem s1SlabData32_center_valid : ∀ i, (s1SlabData32.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1SlabExp11_valid
  · exact s1SlabExp11_valid
  · exact s1SlabExp2_valid


theorem s1SlabData32_margin : 0 < s1SlabData32.cachedDyadicMargin := by decide +kernel

theorem s1SlabBox32_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox32.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData32.dyadic_positive s1SlabData32_lower_valid s1SlabData32_upper_valid
    s1SlabData32_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData32_margin) hq

theorem s1SlabBox31_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox31.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData31.dyadic_positive s1SlabData31_lower_valid s1SlabData31_upper_valid
    s1SlabData31_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData31_margin) hq

theorem s1SlabBox30_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox30.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox30.left 1 (47201/4096 : ℚ) = s1SlabBox31 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox30.right 1 (47201/4096 : ℚ) = s1SlabBox32 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox30.mem_left_or_right hq 1 (47201/4096 : ℚ) with h | h

  · exact s1SlabBox31_positive (hl ▸ h)

  · exact s1SlabBox32_positive (hr ▸ h)

theorem s1SlabBox29_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox29.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData29.dyadic_positive s1SlabData29_lower_valid s1SlabData29_upper_valid
    s1SlabData29_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData29_margin) hq

theorem s1SlabBox28_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox28.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData28.dyadic_positive s1SlabData28_lower_valid s1SlabData28_upper_valid
    s1SlabData28_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData28_margin) hq

theorem s1SlabBox27_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox27.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox27.left 1 (33715/4096 : ℚ) = s1SlabBox28 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox27.right 1 (33715/4096 : ℚ) = s1SlabBox29 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox27.mem_left_or_right hq 1 (33715/4096 : ℚ) with h | h

  · exact s1SlabBox28_positive (hl ▸ h)

  · exact s1SlabBox29_positive (hr ▸ h)

theorem s1SlabBox26_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox26.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox26.left 1 (20229/2048 : ℚ) = s1SlabBox27 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox26.right 1 (20229/2048 : ℚ) = s1SlabBox30 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox26.mem_left_or_right hq 1 (20229/2048 : ℚ) with h | h

  · exact s1SlabBox27_positive (hl ▸ h)

  · exact s1SlabBox30_positive (hr ▸ h)

theorem s1SlabBox25_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox25.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData25.dyadic_positive s1SlabData25_lower_valid s1SlabData25_upper_valid
    s1SlabData25_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData25_margin) hq

theorem s1SlabBox24_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox24.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData24.dyadic_positive s1SlabData24_lower_valid s1SlabData24_upper_valid
    s1SlabData24_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData24_margin) hq

theorem s1SlabBox23_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox23.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox23.left 1 (47201/4096 : ℚ) = s1SlabBox24 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox23.right 1 (47201/4096 : ℚ) = s1SlabBox25 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox23.mem_left_or_right hq 1 (47201/4096 : ℚ) with h | h

  · exact s1SlabBox24_positive (hl ▸ h)

  · exact s1SlabBox25_positive (hr ▸ h)

theorem s1SlabBox22_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox22.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData22.dyadic_positive s1SlabData22_lower_valid s1SlabData22_upper_valid
    s1SlabData22_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData22_margin) hq

theorem s1SlabBox21_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox21.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData21.dyadic_positive s1SlabData21_lower_valid s1SlabData21_upper_valid
    s1SlabData21_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData21_margin) hq

theorem s1SlabBox20_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox20.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox20.left 1 (33715/4096 : ℚ) = s1SlabBox21 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox20.right 1 (33715/4096 : ℚ) = s1SlabBox22 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox20.mem_left_or_right hq 1 (33715/4096 : ℚ) with h | h

  · exact s1SlabBox21_positive (hl ▸ h)

  · exact s1SlabBox22_positive (hr ▸ h)

theorem s1SlabBox19_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox19.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox19.left 1 (20229/2048 : ℚ) = s1SlabBox20 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox19.right 1 (20229/2048 : ℚ) = s1SlabBox23 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox19.mem_left_or_right hq 1 (20229/2048 : ℚ) with h | h

  · exact s1SlabBox20_positive (hl ▸ h)

  · exact s1SlabBox23_positive (hr ▸ h)

theorem s1SlabBox18_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox18.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox18.left 0 (47201/4096 : ℚ) = s1SlabBox19 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox18.right 0 (47201/4096 : ℚ) = s1SlabBox26 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox18.mem_left_or_right hq 0 (47201/4096 : ℚ) with h | h

  · exact s1SlabBox19_positive (hl ▸ h)

  · exact s1SlabBox26_positive (hr ▸ h)

theorem s1SlabBox17_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox17.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData17.dyadic_positive s1SlabData17_lower_valid s1SlabData17_upper_valid
    s1SlabData17_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData17_margin) hq

theorem s1SlabBox16_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox16.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData16.dyadic_positive s1SlabData16_lower_valid s1SlabData16_upper_valid
    s1SlabData16_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData16_margin) hq

theorem s1SlabBox15_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox15.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox15.left 1 (47201/4096 : ℚ) = s1SlabBox16 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox15.right 1 (47201/4096 : ℚ) = s1SlabBox17 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox15.mem_left_or_right hq 1 (47201/4096 : ℚ) with h | h

  · exact s1SlabBox16_positive (hl ▸ h)

  · exact s1SlabBox17_positive (hr ▸ h)

theorem s1SlabBox14_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox14.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData14.dyadic_positive s1SlabData14_lower_valid s1SlabData14_upper_valid
    s1SlabData14_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData14_margin) hq

theorem s1SlabBox13_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox13.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData13.dyadic_positive s1SlabData13_lower_valid s1SlabData13_upper_valid
    s1SlabData13_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData13_margin) hq

theorem s1SlabBox12_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox12.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox12.left 1 (33715/4096 : ℚ) = s1SlabBox13 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox12.right 1 (33715/4096 : ℚ) = s1SlabBox14 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox12.mem_left_or_right hq 1 (33715/4096 : ℚ) with h | h

  · exact s1SlabBox13_positive (hl ▸ h)

  · exact s1SlabBox14_positive (hr ▸ h)

theorem s1SlabBox11_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox11.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox11.left 1 (20229/2048 : ℚ) = s1SlabBox12 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox11.right 1 (20229/2048 : ℚ) = s1SlabBox15 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox11.mem_left_or_right hq 1 (20229/2048 : ℚ) with h | h

  · exact s1SlabBox12_positive (hl ▸ h)

  · exact s1SlabBox15_positive (hr ▸ h)

theorem s1SlabBox10_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox10.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData10.dyadic_positive s1SlabData10_lower_valid s1SlabData10_upper_valid
    s1SlabData10_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData10_margin) hq

theorem s1SlabBox9_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox9.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData9.dyadic_positive s1SlabData9_lower_valid s1SlabData9_upper_valid
    s1SlabData9_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData9_margin) hq

theorem s1SlabBox8_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox8.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox8.left 1 (47201/4096 : ℚ) = s1SlabBox9 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox8.right 1 (47201/4096 : ℚ) = s1SlabBox10 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox8.mem_left_or_right hq 1 (47201/4096 : ℚ) with h | h

  · exact s1SlabBox9_positive (hl ▸ h)

  · exact s1SlabBox10_positive (hr ▸ h)

theorem s1SlabBox7_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox7.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData7.dyadic_positive s1SlabData7_lower_valid s1SlabData7_upper_valid
    s1SlabData7_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData7_margin) hq

theorem s1SlabBox6_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox6.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData6.dyadic_positive s1SlabData6_lower_valid s1SlabData6_upper_valid
    s1SlabData6_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData6_margin) hq

theorem s1SlabBox5_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox5.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  exact s1SlabData5.dyadic_positive s1SlabData5_lower_valid s1SlabData5_upper_valid
    s1SlabData5_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by rw [S1TaylorBoxData.dyadicMargin_eq_cached]; exact s1SlabData5_margin) hq

theorem s1SlabBox4_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox4.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox4.left 2 (47201/8192 : ℚ) = s1SlabBox5 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox4.right 2 (47201/8192 : ℚ) = s1SlabBox6 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox4.mem_left_or_right hq 2 (47201/8192 : ℚ) with h | h

  · exact s1SlabBox5_positive (hl ▸ h)

  · exact s1SlabBox6_positive (hr ▸ h)

theorem s1SlabBox3_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox3.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox3.left 1 (33715/4096 : ℚ) = s1SlabBox4 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox3.right 1 (33715/4096 : ℚ) = s1SlabBox7 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox3.mem_left_or_right hq 1 (33715/4096 : ℚ) with h | h

  · exact s1SlabBox4_positive (hl ▸ h)

  · exact s1SlabBox7_positive (hr ▸ h)

theorem s1SlabBox2_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox2.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox2.left 1 (20229/2048 : ℚ) = s1SlabBox3 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox2.right 1 (20229/2048 : ℚ) = s1SlabBox8 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox2.mem_left_or_right hq 1 (20229/2048 : ℚ) with h | h

  · exact s1SlabBox3_positive (hl ▸ h)

  · exact s1SlabBox8_positive (hr ▸ h)

theorem s1SlabBox1_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox1.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox1.left 0 (33715/4096 : ℚ) = s1SlabBox2 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox1.right 0 (33715/4096 : ℚ) = s1SlabBox11 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox1.mem_left_or_right hq 0 (33715/4096 : ℚ) with h | h

  · exact s1SlabBox2_positive (hl ▸ h)

  · exact s1SlabBox11_positive (hr ▸ h)

theorem s1SlabBox0_positive {q : EdgeTriple} (hq : q ∈ s1SlabBox0.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by

  have hl : s1SlabBox0.left 0 (20229/2048 : ℚ) = s1SlabBox1 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  have hr : s1SlabBox0.right 0 (20229/2048 : ℚ) = s1SlabBox18 :=
    LogBox.eq_of_sameEndpoints (by decide +kernel)

  rcases s1SlabBox0.mem_left_or_right hq 0 (20229/2048 : ℚ) with h | h

  · exact s1SlabBox1_positive (hl ▸ h)

  · exact s1SlabBox18_positive (hr ▸ h)

/-- Positivity throughout `[Q/2,Q]² × [3Q/8,Q/2]`, where Q=6743/512.
This also proves its entire intersection with the ordered logarithmic domain. -/
theorem coverS1_taylor_slab_positive {q : EdgeTriple}
    (hq : q ∈ s1SlabBox0.region) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q :=
  s1SlabBox0_positive hq

end SparseLowerTail.Section05
