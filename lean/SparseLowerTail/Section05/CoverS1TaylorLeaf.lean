import SparseLowerTail.Section05.CoverS1TaylorBox
import SparseLowerTail.Numerics.ExpEndpoints
import SparseLowerTail.Section05.CoverConstantDigits

/-! First actual Taylor2 leaf for the original S1 certificate.
The parameter vertex and all coefficients remain the exact release data. -/
namespace SparseLowerTail.Section05
open Section04 Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000


def s1TaylorEndpoint0 : ExpEndpointCertificate :=
  ⟨(47201/4096 : ℚ),20,(561058027581080725/1152921504606846976 : ℚ),(280529013790540363/576460752303423488 : ℚ),(5702934668567/576460752303423488 : ℚ),(11405869337135/1152921504606846976 : ℚ)⟩

theorem s1TaylorEndpoint0_valid : s1TaylorEndpoint0.Valid := by decide +kernel

def s1TaylorEndpoint1 : ExpEndpointCertificate :=
  ⟨(20229/4096 : ℚ),20,(423366068169979813/576460752303423488 : ℚ),(846732136339959627/1152921504606846976 : ℚ),(2064812399200203/288230376151711744 : ℚ),(8259249596800813/1152921504606846976 : ℚ)⟩

theorem s1TaylorEndpoint1_valid : s1TaylorEndpoint1.Valid := by decide +kernel

def s1TaylorEndpoint2 : ExpEndpointCertificate :=
  ⟨(6743/512 : ℚ),20,(253100626015152875/576460752303423488 : ℚ),(506201252030305751/1152921504606846976 : ℚ),(1099373708893/576460752303423488 : ℚ),(2198747417787/1152921504606846976 : ℚ)⟩

theorem s1TaylorEndpoint2_valid : s1TaylorEndpoint2.Valid := by decide +kernel

def s1TaylorEndpoint3 : ExpEndpointCertificate :=
  ⟨(6743/1024 : ℚ),20,(381971958762894615/576460752303423488 : ℚ),(763943917525789231/1152921504606846976 : ℚ),(796081525530615/576460752303423488 : ℚ),(1592163051061231/1152921504606846976 : ℚ)⟩

theorem s1TaylorEndpoint3_valid : s1TaylorEndpoint3.Valid := by decide +kernel

def s1TaylorEndpoint4 : ExpEndpointCertificate :=
  ⟨(101145/8192 : ℚ),20,(266462134281400703/576460752303423488 : ℚ),(532924268562801407/1152921504606846976 : ℚ),(1251964100739/288230376151711744 : ℚ),(5007856402957/1152921504606846976 : ℚ)⟩

theorem s1TaylorEndpoint4_valid : s1TaylorEndpoint4.Valid := by decide +kernel

def s1TaylorEndpoint5 : ExpEndpointCertificate :=
  ⟨(47201/8192 : ℚ),20,(201068375392944601/288230376151711744 : ℚ),(804273501571778405/1152921504606846976 : ℚ),(3626302805547079/1152921504606846976 : ℚ),(453287850693385/144115188075855872 : ℚ)⟩

theorem s1TaylorEndpoint5_valid : s1TaylorEndpoint5.Valid := by decide +kernel

def s1TaylorLeafBox : LogBox := ⟨![(47201/4096 : ℚ),(47201/4096 : ℚ),(20229/4096 : ℚ)],![(6743/512 : ℚ),(6743/512 : ℚ),(6743/1024 : ℚ)]⟩

def s1TaylorLeafData : S1TaylorBoxData :=
  ⟨s1TaylorLeafBox,![s1TaylorEndpoint0,s1TaylorEndpoint0,s1TaylorEndpoint1],![s1TaylorEndpoint2,s1TaylorEndpoint2,s1TaylorEndpoint3],![s1TaylorEndpoint4,s1TaylorEndpoint4,s1TaylorEndpoint5]⟩

theorem s1TaylorLeaf_lower_valid : ∀ i, (s1TaylorLeafData.lowerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1TaylorEndpoint0_valid
  · exact s1TaylorEndpoint0_valid
  · exact s1TaylorEndpoint1_valid


theorem s1TaylorLeaf_upper_valid : ∀ i, (s1TaylorLeafData.upperExp i).Valid := by
  intro i
  fin_cases i
  · exact s1TaylorEndpoint2_valid
  · exact s1TaylorEndpoint2_valid
  · exact s1TaylorEndpoint3_valid


theorem s1TaylorLeaf_center_valid : ∀ i, (s1TaylorLeafData.centerExp i).Valid := by
  intro i
  fin_cases i
  · exact s1TaylorEndpoint4_valid
  · exact s1TaylorEndpoint4_valid
  · exact s1TaylorEndpoint5_valid


theorem s1Taylor_rational_check : (1/100:ℚ) < s1TaylorLeafData.margin := by
  decide +kernel

/-- Actual certified positivity on a full original Taylor2 leaf, not merely
on sampled points or on a conditional interval enclosure. -/
theorem coverS1_taylor_leaf_positive {q : EdgeTriple} (hq : q ∈ s1TaylorLeafBox.region) :
    (1/100:ℝ) < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q := by
  have h := s1TaylorLeafData.positive s1TaylorLeaf_lower_valid s1TaylorLeaf_upper_valid
    s1TaylorLeaf_center_valid (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s1Taylor_rational_check hq
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

end SparseLowerTail.Section05
