import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0000
import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0002
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1.Boxes000

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data0 : S1TaylorBoxData := ⟨box0,![exp0,exp0,exp0],![exp16,exp16,exp16],![exp8,exp8,exp8]⟩
theorem data0_lower_valid : ∀ j, (data0.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp0_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data0_upper_valid : ∀ j, (data0.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp16_valid
  · exact exp16_valid
theorem data0_center_valid : ∀ j, (data0.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp8_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin0 : 0 < data0.apexRefinedMargin 0 := by decide +kernel
theorem conclusion0 {q : EdgeTriple} (hq : q ∈ box0.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data0.apexRefined_positive 0
    data0_lower_valid data0_upper_valid data0_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin0 hq

def data1 : S1TaylorBoxData := ⟨box1,![exp16,exp0,exp0],![exp148,exp148,exp148],![exp32,exp16,exp16]⟩
theorem data1_lower_valid : ∀ j, (data1.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp16_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data1_upper_valid : ∀ j, (data1.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp148_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data1_center_valid : ∀ j, (data1.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp32_valid
  · exact exp16_valid
  · exact exp16_valid
theorem margin1 : 0 < data1.apexRefinedMargin 0 := by decide +kernel
theorem conclusion1 {q : EdgeTriple} (hq : q ∈ box1.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data1.apexRefined_positive 0
    data1_lower_valid data1_upper_valid data1_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin1 hq

def data2 : S1TaylorBoxData := ⟨box2,![exp148,exp0,exp0],![exp166,exp148,exp148],![exp158,exp16,exp16]⟩
theorem data2_lower_valid : ∀ j, (data2.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp148_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data2_upper_valid : ∀ j, (data2.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data2_center_valid : ∀ j, (data2.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp158_valid
  · exact exp16_valid
  · exact exp16_valid
theorem margin2 : 0 < data2.apexRefinedMargin 0 := by decide +kernel
theorem conclusion2 {q : EdgeTriple} (hq : q ∈ box2.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data2.apexRefined_positive 0
    data2_lower_valid data2_upper_valid data2_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin2 hq

def data3 : S1TaylorBoxData := ⟨box3,![exp166,exp0,exp0],![exp174,exp16,exp16],![exp170,exp8,exp8]⟩
theorem data3_lower_valid : ∀ j, (data3.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data3_upper_valid : ∀ j, (data3.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp16_valid
  · exact exp16_valid
theorem data3_center_valid : ∀ j, (data3.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin3 : 0 < data3.apexRefinedMargin 0 := by decide +kernel
theorem conclusion3 {q : EdgeTriple} (hq : q ∈ box3.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data3.apexRefined_positive 0
    data3_lower_valid data3_upper_valid data3_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin3 hq

def data4 : S1TaylorBoxData := ⟨box4,![exp166,exp16,exp0],![exp174,exp148,exp148],![exp170,exp32,exp16]⟩
theorem data4_lower_valid : ∀ j, (data4.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp16_valid
  · exact exp0_valid
theorem data4_upper_valid : ∀ j, (data4.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data4_center_valid : ∀ j, (data4.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp32_valid
  · exact exp16_valid
theorem margin4 : 0 < data4.apexRefinedMargin 0 := by decide +kernel
theorem conclusion4 {q : EdgeTriple} (hq : q ∈ box4.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data4.apexRefined_positive 0
    data4_lower_valid data4_upper_valid data4_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin4 hq

def data5 : S1TaylorBoxData := ⟨box5,![exp148,exp148,exp0],![exp166,exp166,exp148],![exp158,exp158,exp16]⟩
theorem data5_lower_valid : ∀ j, (data5.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp148_valid
  · exact exp148_valid
  · exact exp0_valid
theorem data5_upper_valid : ∀ j, (data5.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp166_valid
  · exact exp148_valid
theorem data5_center_valid : ∀ j, (data5.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp158_valid
  · exact exp158_valid
  · exact exp16_valid
theorem margin5 : 0 < data5.apexRefinedMargin 0 := by decide +kernel
theorem conclusion5 {q : EdgeTriple} (hq : q ∈ box5.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data5.apexRefined_positive 0
    data5_lower_valid data5_upper_valid data5_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin5 hq

def data6 : S1TaylorBoxData := ⟨box6,![exp166,exp148,exp0],![exp174,exp166,exp148],![exp170,exp158,exp16]⟩
theorem data6_lower_valid : ∀ j, (data6.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp148_valid
  · exact exp0_valid
theorem data6_upper_valid : ∀ j, (data6.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp166_valid
  · exact exp148_valid
theorem data6_center_valid : ∀ j, (data6.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp158_valid
  · exact exp16_valid
theorem margin6 : 0 < data6.apexRefinedMargin 0 := by decide +kernel
theorem conclusion6 {q : EdgeTriple} (hq : q ∈ box6.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data6.apexRefined_positive 0
    data6_lower_valid data6_upper_valid data6_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin6 hq

def data7 : S1TaylorBoxData := ⟨box7,![exp166,exp166,exp0],![exp174,exp174,exp148],![exp170,exp170,exp16]⟩
theorem data7_lower_valid : ∀ j, (data7.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp166_valid
  · exact exp0_valid
theorem data7_upper_valid : ∀ j, (data7.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp174_valid
  · exact exp148_valid
theorem data7_center_valid : ∀ j, (data7.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp170_valid
  · exact exp16_valid
theorem margin7 : 0 < data7.apexRefinedMargin 0 := by decide +kernel
theorem conclusion7 {q : EdgeTriple} (hq : q ∈ box7.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data7.apexRefined_positive 0
    data7_lower_valid data7_upper_valid data7_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin7 hq

def data8 : S1TaylorBoxData := ⟨box8,![exp148,exp148,exp148],![exp166,exp166,exp166],![exp158,exp158,exp158]⟩
theorem data8_lower_valid : ∀ j, (data8.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp148_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data8_upper_valid : ∀ j, (data8.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp166_valid
  · exact exp166_valid
theorem data8_center_valid : ∀ j, (data8.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp158_valid
  · exact exp158_valid
  · exact exp158_valid
theorem margin8 : 0 < data8.apexRefinedMargin 0 := by decide +kernel
theorem conclusion8 {q : EdgeTriple} (hq : q ∈ box8.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data8.apexRefined_positive 0
    data8_lower_valid data8_upper_valid data8_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin8 hq

def data9 : S1TaylorBoxData := ⟨box9,![exp166,exp148,exp148],![exp174,exp166,exp166],![exp170,exp158,exp158]⟩
theorem data9_lower_valid : ∀ j, (data9.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data9_upper_valid : ∀ j, (data9.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp166_valid
  · exact exp166_valid
theorem data9_center_valid : ∀ j, (data9.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp158_valid
  · exact exp158_valid
theorem margin9 : 0 < data9.apexRefinedMargin 0 := by decide +kernel
theorem conclusion9 {q : EdgeTriple} (hq : q ∈ box9.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data9.apexRefined_positive 0
    data9_lower_valid data9_upper_valid data9_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin9 hq

def data10 : S1TaylorBoxData := ⟨box10,![exp166,exp166,exp148],![exp174,exp174,exp174],![exp170,exp170,exp166]⟩
theorem data10_lower_valid : ∀ j, (data10.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp166_valid
  · exact exp166_valid
  · exact exp148_valid
theorem data10_upper_valid : ∀ j, (data10.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp174_valid
  · exact exp174_valid
theorem data10_center_valid : ∀ j, (data10.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp170_valid
  · exact exp170_valid
  · exact exp166_valid
theorem margin10 : 0 < data10.apexRefinedMargin 0 := by decide +kernel
theorem conclusion10 {q : EdgeTriple} (hq : q ∈ box10.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data10.apexRefined_positive 0
    data10_lower_valid data10_upper_valid data10_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin10 hq

def data11 : S1TaylorBoxData := ⟨box11,![exp174,exp0,exp0],![exp182,exp16,exp16],![exp178,exp8,exp8]⟩
theorem data11_lower_valid : ∀ j, (data11.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data11_upper_valid : ∀ j, (data11.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp182_valid
  · exact exp16_valid
  · exact exp16_valid
theorem data11_center_valid : ∀ j, (data11.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp178_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin11 : 0 < data11.apexRefinedMargin 0 := by decide +kernel
theorem conclusion11 {q : EdgeTriple} (hq : q ∈ box11.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data11.apexRefined_positive 0
    data11_lower_valid data11_upper_valid data11_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin11 hq

def data12 : S1TaylorBoxData := ⟨box12,![exp174,exp16,exp0],![exp182,exp148,exp148],![exp178,exp32,exp16]⟩
theorem data12_lower_valid : ∀ j, (data12.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp16_valid
  · exact exp0_valid
theorem data12_upper_valid : ∀ j, (data12.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp182_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data12_center_valid : ∀ j, (data12.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp178_valid
  · exact exp32_valid
  · exact exp16_valid
theorem margin12 : 0 < data12.apexRefinedMargin 0 := by decide +kernel
theorem conclusion12 {q : EdgeTriple} (hq : q ∈ box12.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data12.apexRefined_positive 0
    data12_lower_valid data12_upper_valid data12_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin12 hq

def data13 : S1TaylorBoxData := ⟨box13,![exp182,exp0,exp0],![exp186,exp16,exp16],![exp184,exp8,exp8]⟩
theorem data13_lower_valid : ∀ j, (data13.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp182_valid
  · exact exp0_valid
  · exact exp0_valid
theorem data13_upper_valid : ∀ j, (data13.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp186_valid
  · exact exp16_valid
  · exact exp16_valid
theorem data13_center_valid : ∀ j, (data13.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp184_valid
  · exact exp8_valid
  · exact exp8_valid
theorem margin13 : 0 < data13.apexRefinedMargin 0 := by decide +kernel
theorem conclusion13 {q : EdgeTriple} (hq : q ∈ box13.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data13.apexRefined_positive 0
    data13_lower_valid data13_upper_valid data13_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin13 hq

def data14 : S1TaylorBoxData := ⟨box14,![exp182,exp16,exp0],![exp186,exp148,exp148],![exp184,exp32,exp16]⟩
theorem data14_lower_valid : ∀ j, (data14.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp182_valid
  · exact exp16_valid
  · exact exp0_valid
theorem data14_upper_valid : ∀ j, (data14.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp186_valid
  · exact exp148_valid
  · exact exp148_valid
theorem data14_center_valid : ∀ j, (data14.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp184_valid
  · exact exp32_valid
  · exact exp16_valid
theorem margin14 : 0 < data14.apexRefinedMargin 0 := by decide +kernel
theorem conclusion14 {q : EdgeTriple} (hq : q ∈ box14.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data14.apexRefined_positive 0
    data14_lower_valid data14_upper_valid data14_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin14 hq

def data15 : S1TaylorBoxData := ⟨box15,![exp174,exp148,exp0],![exp182,exp166,exp148],![exp178,exp158,exp16]⟩
theorem data15_lower_valid : ∀ j, (data15.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp174_valid
  · exact exp148_valid
  · exact exp0_valid
theorem data15_upper_valid : ∀ j, (data15.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp182_valid
  · exact exp166_valid
  · exact exp148_valid
theorem data15_center_valid : ∀ j, (data15.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp178_valid
  · exact exp158_valid
  · exact exp16_valid
theorem margin15 : 0 < data15.apexRefinedMargin 0 := by decide +kernel
theorem conclusion15 {q : EdgeTriple} (hq : q ∈ box15.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data15.apexRefined_positive 0
    data15_lower_valid data15_upper_valid data15_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin15 hq

end SparseLowerTail.Section05.ApexReplay.F1
