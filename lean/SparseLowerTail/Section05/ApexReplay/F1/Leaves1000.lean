import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0000
import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0001
import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0009
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1.Boxes062

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data16000 : S1TaylorBoxData := ⟨box16000,![exp598,exp98,exp94],![exp600,exp100,exp98],![exp599,exp99,exp96]⟩
theorem data16000_lower_valid : ∀ j, (data16000.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp98_valid
  · exact exp94_valid
theorem data16000_upper_valid : ∀ j, (data16000.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp600_valid
  · exact exp100_valid
  · exact exp98_valid
theorem data16000_center_valid : ∀ j, (data16000.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp599_valid
  · exact exp99_valid
  · exact exp96_valid
theorem margin16000 : 0 < data16000.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16000 {q : EdgeTriple} (hq : q ∈ box16000.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16000.apexRefined_positive 0
    data16000_lower_valid data16000_upper_valid data16000_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16000 hq

def data16001 : S1TaylorBoxData := ⟨box16001,![exp598,exp100,exp88],![exp600,exp102,exp98],![exp599,exp101,exp94]⟩
theorem data16001_lower_valid : ∀ j, (data16001.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp100_valid
  · exact exp88_valid
theorem data16001_upper_valid : ∀ j, (data16001.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp600_valid
  · exact exp102_valid
  · exact exp98_valid
theorem data16001_center_valid : ∀ j, (data16001.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp599_valid
  · exact exp101_valid
  · exact exp94_valid
theorem margin16001 : 0 < data16001.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16001 {q : EdgeTriple} (hq : q ∈ box16001.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16001.apexRefined_positive 0
    data16001_lower_valid data16001_upper_valid data16001_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16001 hq

def data16002 : S1TaylorBoxData := ⟨box16002,![exp596,exp98,exp98],![exp598,exp100,exp100],![exp597,exp99,exp99]⟩
theorem data16002_lower_valid : ∀ j, (data16002.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp596_valid
  · exact exp98_valid
  · exact exp98_valid
theorem data16002_upper_valid : ∀ j, (data16002.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp100_valid
  · exact exp100_valid
theorem data16002_center_valid : ∀ j, (data16002.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp597_valid
  · exact exp99_valid
  · exact exp99_valid
theorem margin16002 : 0 < data16002.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16002 {q : EdgeTriple} (hq : q ∈ box16002.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16002.apexRefined_positive 0
    data16002_lower_valid data16002_upper_valid data16002_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16002 hq

def data16003 : S1TaylorBoxData := ⟨box16003,![exp596,exp100,exp98],![exp598,exp102,exp102],![exp597,exp101,exp100]⟩
theorem data16003_lower_valid : ∀ j, (data16003.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp596_valid
  · exact exp100_valid
  · exact exp98_valid
theorem data16003_upper_valid : ∀ j, (data16003.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp102_valid
  · exact exp102_valid
theorem data16003_center_valid : ∀ j, (data16003.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp597_valid
  · exact exp101_valid
  · exact exp100_valid
theorem margin16003 : 0 < data16003.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16003 {q : EdgeTriple} (hq : q ∈ box16003.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16003.apexRefined_positive 0
    data16003_lower_valid data16003_upper_valid data16003_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16003 hq

def data16004 : S1TaylorBoxData := ⟨box16004,![exp598,exp98,exp98],![exp600,exp100,exp100],![exp599,exp99,exp99]⟩
theorem data16004_lower_valid : ∀ j, (data16004.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp98_valid
  · exact exp98_valid
theorem data16004_upper_valid : ∀ j, (data16004.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp600_valid
  · exact exp100_valid
  · exact exp100_valid
theorem data16004_center_valid : ∀ j, (data16004.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp599_valid
  · exact exp99_valid
  · exact exp99_valid
theorem margin16004 : 0 < data16004.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16004 {q : EdgeTriple} (hq : q ∈ box16004.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16004.apexRefined_positive 0
    data16004_lower_valid data16004_upper_valid data16004_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16004 hq

def data16005 : S1TaylorBoxData := ⟨box16005,![exp598,exp100,exp98],![exp600,exp102,exp102],![exp599,exp101,exp100]⟩
theorem data16005_lower_valid : ∀ j, (data16005.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp598_valid
  · exact exp100_valid
  · exact exp98_valid
theorem data16005_upper_valid : ∀ j, (data16005.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp600_valid
  · exact exp102_valid
  · exact exp102_valid
theorem data16005_center_valid : ∀ j, (data16005.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp599_valid
  · exact exp101_valid
  · exact exp100_valid
theorem margin16005 : 0 < data16005.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16005 {q : EdgeTriple} (hq : q ∈ box16005.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16005.apexRefined_positive 0
    data16005_lower_valid data16005_upper_valid data16005_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16005 hq

def data16006 : S1TaylorBoxData := ⟨box16006,![exp584,exp102,exp62],![exp588,exp106,exp72],![exp586,exp104,exp66]⟩
theorem data16006_lower_valid : ∀ j, (data16006.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp584_valid
  · exact exp102_valid
  · exact exp62_valid
theorem data16006_upper_valid : ∀ j, (data16006.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp106_valid
  · exact exp72_valid
theorem data16006_center_valid : ∀ j, (data16006.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp104_valid
  · exact exp66_valid
theorem margin16006 : 0 < data16006.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16006 {q : EdgeTriple} (hq : q ∈ box16006.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16006.apexRefined_positive 0
    data16006_lower_valid data16006_upper_valid data16006_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16006 hq

def data16007 : S1TaylorBoxData := ⟨box16007,![exp584,exp102,exp72],![exp588,exp106,exp88],![exp586,exp104,exp80]⟩
theorem data16007_lower_valid : ∀ j, (data16007.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp584_valid
  · exact exp102_valid
  · exact exp72_valid
theorem data16007_upper_valid : ∀ j, (data16007.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp106_valid
  · exact exp88_valid
theorem data16007_center_valid : ∀ j, (data16007.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp104_valid
  · exact exp80_valid
theorem margin16007 : 0 < data16007.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16007 {q : EdgeTriple} (hq : q ∈ box16007.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16007.apexRefined_positive 0
    data16007_lower_valid data16007_upper_valid data16007_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16007 hq

def data16008 : S1TaylorBoxData := ⟨box16008,![exp584,exp106,exp62],![exp588,exp108,exp88],![exp586,exp107,exp72]⟩
theorem data16008_lower_valid : ∀ j, (data16008.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp584_valid
  · exact exp106_valid
  · exact exp62_valid
theorem data16008_upper_valid : ∀ j, (data16008.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp108_valid
  · exact exp88_valid
theorem data16008_center_valid : ∀ j, (data16008.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp107_valid
  · exact exp72_valid
theorem margin16008 : 0 < data16008.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16008 {q : EdgeTriple} (hq : q ∈ box16008.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16008.apexRefined_positive 0
    data16008_lower_valid data16008_upper_valid data16008_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16008 hq

def data16009 : S1TaylorBoxData := ⟨box16009,![exp588,exp102,exp62],![exp592,exp106,exp72],![exp590,exp104,exp66]⟩
theorem data16009_lower_valid : ∀ j, (data16009.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp102_valid
  · exact exp62_valid
theorem data16009_upper_valid : ∀ j, (data16009.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp592_valid
  · exact exp106_valid
  · exact exp72_valid
theorem data16009_center_valid : ∀ j, (data16009.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp590_valid
  · exact exp104_valid
  · exact exp66_valid
theorem margin16009 : 0 < data16009.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16009 {q : EdgeTriple} (hq : q ∈ box16009.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16009.apexRefined_positive 0
    data16009_lower_valid data16009_upper_valid data16009_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16009 hq

def data16010 : S1TaylorBoxData := ⟨box16010,![exp588,exp102,exp72],![exp592,exp106,exp88],![exp590,exp104,exp80]⟩
theorem data16010_lower_valid : ∀ j, (data16010.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp102_valid
  · exact exp72_valid
theorem data16010_upper_valid : ∀ j, (data16010.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp592_valid
  · exact exp106_valid
  · exact exp88_valid
theorem data16010_center_valid : ∀ j, (data16010.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp590_valid
  · exact exp104_valid
  · exact exp80_valid
theorem margin16010 : 0 < data16010.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16010 {q : EdgeTriple} (hq : q ∈ box16010.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16010.apexRefined_positive 0
    data16010_lower_valid data16010_upper_valid data16010_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16010 hq

def data16011 : S1TaylorBoxData := ⟨box16011,![exp588,exp106,exp62],![exp592,exp108,exp72],![exp590,exp107,exp66]⟩
theorem data16011_lower_valid : ∀ j, (data16011.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp106_valid
  · exact exp62_valid
theorem data16011_upper_valid : ∀ j, (data16011.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp592_valid
  · exact exp108_valid
  · exact exp72_valid
theorem data16011_center_valid : ∀ j, (data16011.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp590_valid
  · exact exp107_valid
  · exact exp66_valid
theorem margin16011 : 0 < data16011.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16011 {q : EdgeTriple} (hq : q ∈ box16011.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16011.apexRefined_positive 0
    data16011_lower_valid data16011_upper_valid data16011_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16011 hq

def data16012 : S1TaylorBoxData := ⟨box16012,![exp588,exp106,exp72],![exp592,exp108,exp88],![exp590,exp107,exp80]⟩
theorem data16012_lower_valid : ∀ j, (data16012.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp106_valid
  · exact exp72_valid
theorem data16012_upper_valid : ∀ j, (data16012.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp592_valid
  · exact exp108_valid
  · exact exp88_valid
theorem data16012_center_valid : ∀ j, (data16012.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp590_valid
  · exact exp107_valid
  · exact exp80_valid
theorem margin16012 : 0 < data16012.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16012 {q : EdgeTriple} (hq : q ∈ box16012.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16012.apexRefined_positive 0
    data16012_lower_valid data16012_upper_valid data16012_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16012 hq

def data16013 : S1TaylorBoxData := ⟨box16013,![exp584,exp102,exp88],![exp586,exp106,exp98],![exp585,exp104,exp94]⟩
theorem data16013_lower_valid : ∀ j, (data16013.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp584_valid
  · exact exp102_valid
  · exact exp88_valid
theorem data16013_upper_valid : ∀ j, (data16013.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp106_valid
  · exact exp98_valid
theorem data16013_center_valid : ∀ j, (data16013.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp585_valid
  · exact exp104_valid
  · exact exp94_valid
theorem margin16013 : 0 < data16013.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16013 {q : EdgeTriple} (hq : q ∈ box16013.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16013.apexRefined_positive 0
    data16013_lower_valid data16013_upper_valid data16013_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16013 hq

def data16014 : S1TaylorBoxData := ⟨box16014,![exp586,exp102,exp88],![exp588,exp104,exp98],![exp587,exp103,exp94]⟩
theorem data16014_lower_valid : ∀ j, (data16014.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp102_valid
  · exact exp88_valid
theorem data16014_upper_valid : ∀ j, (data16014.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp104_valid
  · exact exp98_valid
theorem data16014_center_valid : ∀ j, (data16014.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp587_valid
  · exact exp103_valid
  · exact exp94_valid
theorem margin16014 : 0 < data16014.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16014 {q : EdgeTriple} (hq : q ∈ box16014.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16014.apexRefined_positive 0
    data16014_lower_valid data16014_upper_valid data16014_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16014 hq

def data16015 : S1TaylorBoxData := ⟨box16015,![exp586,exp104,exp88],![exp588,exp106,exp98],![exp587,exp105,exp94]⟩
theorem data16015_lower_valid : ∀ j, (data16015.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp586_valid
  · exact exp104_valid
  · exact exp88_valid
theorem data16015_upper_valid : ∀ j, (data16015.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp588_valid
  · exact exp106_valid
  · exact exp98_valid
theorem data16015_center_valid : ∀ j, (data16015.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp587_valid
  · exact exp105_valid
  · exact exp94_valid
theorem margin16015 : 0 < data16015.apexRefinedMargin 0 := by decide +kernel
theorem conclusion16015 {q : EdgeTriple} (hq : q ∈ box16015.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data16015.apexRefined_positive 0
    data16015_lower_valid data16015_upper_valid data16015_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin16015 hq

end SparseLowerTail.Section05.ApexReplay.F1
