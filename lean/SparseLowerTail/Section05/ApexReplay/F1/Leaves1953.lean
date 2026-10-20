import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0015
import SparseLowerTail.Section05.ApexReplay.F1.Endpoints0016
import SparseLowerTail.Section05.ApexCoverAssembly
import SparseLowerTail.Section05.ApexRefinedTaylorBox
import SparseLowerTail.Section05.ApexReplay.F1.Boxes122

/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace SparseLowerTail.Section05.ApexReplay.F1
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def data31248 : S1TaylorBoxData := ⟨box31248,![exp1040,exp968,exp968],![exp1048,exp1000,exp1000],![exp1044,exp984,exp984]⟩
theorem data31248_lower_valid : ∀ j, (data31248.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp968_valid
  · exact exp968_valid
theorem data31248_upper_valid : ∀ j, (data31248.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1000_valid
  · exact exp1000_valid
theorem data31248_center_valid : ∀ j, (data31248.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1044_valid
  · exact exp984_valid
  · exact exp984_valid
theorem margin31248 : 0 < data31248.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31248 {q : EdgeTriple} (hq : q ∈ box31248.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31248.apexRefined_positive 0
    data31248_lower_valid data31248_upper_valid data31248_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31248 hq

def data31249 : S1TaylorBoxData := ⟨box31249,![exp1032,exp1000,exp968],![exp1048,exp1032,exp1000],![exp1040,exp1016,exp984]⟩
theorem data31249_lower_valid : ∀ j, (data31249.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1032_valid
  · exact exp1000_valid
  · exact exp968_valid
theorem data31249_upper_valid : ∀ j, (data31249.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1032_valid
  · exact exp1000_valid
theorem data31249_center_valid : ∀ j, (data31249.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp1016_valid
  · exact exp984_valid
theorem margin31249 : 0 < data31249.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31249 {q : EdgeTriple} (hq : q ∈ box31249.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31249.apexRefined_positive 0
    data31249_lower_valid data31249_upper_valid data31249_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31249 hq

def data31250 : S1TaylorBoxData := ⟨box31250,![exp1032,exp1000,exp1000],![exp1048,exp1032,exp1032],![exp1040,exp1016,exp1016]⟩
theorem data31250_lower_valid : ∀ j, (data31250.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1032_valid
  · exact exp1000_valid
  · exact exp1000_valid
theorem data31250_upper_valid : ∀ j, (data31250.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1032_valid
  · exact exp1032_valid
theorem data31250_center_valid : ∀ j, (data31250.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp1016_valid
  · exact exp1016_valid
theorem margin31250 : 0 < data31250.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31250 {q : EdgeTriple} (hq : q ∈ box31250.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31250.apexRefined_positive 0
    data31250_lower_valid data31250_upper_valid data31250_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31250 hq

def data31251 : S1TaylorBoxData := ⟨box31251,![exp1048,exp968,exp968],![exp1064,exp1000,exp1000],![exp1056,exp984,exp984]⟩
theorem data31251_lower_valid : ∀ j, (data31251.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp968_valid
  · exact exp968_valid
theorem data31251_upper_valid : ∀ j, (data31251.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1000_valid
  · exact exp1000_valid
theorem data31251_center_valid : ∀ j, (data31251.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp984_valid
  · exact exp984_valid
theorem margin31251 : 0 < data31251.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31251 {q : EdgeTriple} (hq : q ∈ box31251.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31251.apexRefined_positive 0
    data31251_lower_valid data31251_upper_valid data31251_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31251 hq

def data31252 : S1TaylorBoxData := ⟨box31252,![exp1048,exp1000,exp968],![exp1064,exp1032,exp1000],![exp1056,exp1016,exp984]⟩
theorem data31252_lower_valid : ∀ j, (data31252.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1000_valid
  · exact exp968_valid
theorem data31252_upper_valid : ∀ j, (data31252.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1032_valid
  · exact exp1000_valid
theorem data31252_center_valid : ∀ j, (data31252.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1016_valid
  · exact exp984_valid
theorem margin31252 : 0 < data31252.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31252 {q : EdgeTriple} (hq : q ∈ box31252.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31252.apexRefined_positive 0
    data31252_lower_valid data31252_upper_valid data31252_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31252 hq

def data31253 : S1TaylorBoxData := ⟨box31253,![exp1048,exp1000,exp1000],![exp1064,exp1032,exp1032],![exp1056,exp1016,exp1016]⟩
theorem data31253_lower_valid : ∀ j, (data31253.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1000_valid
  · exact exp1000_valid
theorem data31253_upper_valid : ∀ j, (data31253.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1032_valid
  · exact exp1032_valid
theorem data31253_center_valid : ∀ j, (data31253.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1016_valid
  · exact exp1016_valid
theorem margin31253 : 0 < data31253.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31253 {q : EdgeTriple} (hq : q ∈ box31253.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31253.apexRefined_positive 0
    data31253_lower_valid data31253_upper_valid data31253_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31253 hq

def data31254 : S1TaylorBoxData := ⟨box31254,![exp1032,exp1032,exp968],![exp1048,exp1048,exp1000],![exp1040,exp1040,exp984]⟩
theorem data31254_lower_valid : ∀ j, (data31254.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1032_valid
  · exact exp1032_valid
  · exact exp968_valid
theorem data31254_upper_valid : ∀ j, (data31254.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp1000_valid
theorem data31254_center_valid : ∀ j, (data31254.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp1040_valid
  · exact exp984_valid
theorem margin31254 : 0 < data31254.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31254 {q : EdgeTriple} (hq : q ∈ box31254.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31254.apexRefined_positive 0
    data31254_lower_valid data31254_upper_valid data31254_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31254 hq

def data31255 : S1TaylorBoxData := ⟨box31255,![exp1032,exp1032,exp1000],![exp1048,exp1048,exp1032],![exp1040,exp1040,exp1016]⟩
theorem data31255_lower_valid : ∀ j, (data31255.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1032_valid
  · exact exp1032_valid
  · exact exp1000_valid
theorem data31255_upper_valid : ∀ j, (data31255.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp1032_valid
theorem data31255_center_valid : ∀ j, (data31255.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp1040_valid
  · exact exp1016_valid
theorem margin31255 : 0 < data31255.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31255 {q : EdgeTriple} (hq : q ∈ box31255.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31255.apexRefined_positive 0
    data31255_lower_valid data31255_upper_valid data31255_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31255 hq

def data31256 : S1TaylorBoxData := ⟨box31256,![exp1048,exp1032,exp968],![exp1064,exp1048,exp1000],![exp1056,exp1040,exp984]⟩
theorem data31256_lower_valid : ∀ j, (data31256.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1032_valid
  · exact exp968_valid
theorem data31256_upper_valid : ∀ j, (data31256.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1048_valid
  · exact exp1000_valid
theorem data31256_center_valid : ∀ j, (data31256.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1040_valid
  · exact exp984_valid
theorem margin31256 : 0 < data31256.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31256 {q : EdgeTriple} (hq : q ∈ box31256.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31256.apexRefined_positive 0
    data31256_lower_valid data31256_upper_valid data31256_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31256 hq

def data31257 : S1TaylorBoxData := ⟨box31257,![exp1048,exp1032,exp1000],![exp1064,exp1048,exp1032],![exp1056,exp1040,exp1016]⟩
theorem data31257_lower_valid : ∀ j, (data31257.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1032_valid
  · exact exp1000_valid
theorem data31257_upper_valid : ∀ j, (data31257.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1048_valid
  · exact exp1032_valid
theorem data31257_center_valid : ∀ j, (data31257.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1040_valid
  · exact exp1016_valid
theorem margin31257 : 0 < data31257.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31257 {q : EdgeTriple} (hq : q ∈ box31257.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31257.apexRefined_positive 0
    data31257_lower_valid data31257_upper_valid data31257_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31257 hq

def data31258 : S1TaylorBoxData := ⟨box31258,![exp1048,exp1048,exp968],![exp1064,exp1064,exp1000],![exp1056,exp1056,exp984]⟩
theorem data31258_lower_valid : ∀ j, (data31258.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp968_valid
theorem data31258_upper_valid : ∀ j, (data31258.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1064_valid
  · exact exp1000_valid
theorem data31258_center_valid : ∀ j, (data31258.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1056_valid
  · exact exp984_valid
theorem margin31258 : 0 < data31258.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31258 {q : EdgeTriple} (hq : q ∈ box31258.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31258.apexRefined_positive 0
    data31258_lower_valid data31258_upper_valid data31258_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31258 hq

def data31259 : S1TaylorBoxData := ⟨box31259,![exp1048,exp1048,exp1000],![exp1064,exp1064,exp1032],![exp1056,exp1056,exp1016]⟩
theorem data31259_lower_valid : ∀ j, (data31259.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp1000_valid
theorem data31259_upper_valid : ∀ j, (data31259.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1064_valid
  · exact exp1032_valid
theorem data31259_center_valid : ∀ j, (data31259.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1056_valid
  · exact exp1016_valid
theorem margin31259 : 0 < data31259.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31259 {q : EdgeTriple} (hq : q ∈ box31259.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31259.apexRefined_positive 0
    data31259_lower_valid data31259_upper_valid data31259_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31259 hq

def data31260 : S1TaylorBoxData := ⟨box31260,![exp1032,exp1032,exp1032],![exp1048,exp1048,exp1048],![exp1040,exp1040,exp1040]⟩
theorem data31260_lower_valid : ∀ j, (data31260.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1032_valid
  · exact exp1032_valid
  · exact exp1032_valid
theorem data31260_upper_valid : ∀ j, (data31260.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp1048_valid
theorem data31260_center_valid : ∀ j, (data31260.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1040_valid
  · exact exp1040_valid
  · exact exp1040_valid
theorem margin31260 : 0 < data31260.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31260 {q : EdgeTriple} (hq : q ∈ box31260.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31260.apexRefined_positive 0
    data31260_lower_valid data31260_upper_valid data31260_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31260 hq

def data31261 : S1TaylorBoxData := ⟨box31261,![exp1048,exp1032,exp1032],![exp1064,exp1048,exp1048],![exp1056,exp1040,exp1040]⟩
theorem data31261_lower_valid : ∀ j, (data31261.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1032_valid
  · exact exp1032_valid
theorem data31261_upper_valid : ∀ j, (data31261.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1048_valid
  · exact exp1048_valid
theorem data31261_center_valid : ∀ j, (data31261.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1040_valid
  · exact exp1040_valid
theorem margin31261 : 0 < data31261.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31261 {q : EdgeTriple} (hq : q ∈ box31261.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31261.apexRefined_positive 0
    data31261_lower_valid data31261_upper_valid data31261_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31261 hq

def data31262 : S1TaylorBoxData := ⟨box31262,![exp1048,exp1048,exp1032],![exp1064,exp1064,exp1064],![exp1056,exp1056,exp1048]⟩
theorem data31262_lower_valid : ∀ j, (data31262.lowerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1048_valid
  · exact exp1048_valid
  · exact exp1032_valid
theorem data31262_upper_valid : ∀ j, (data31262.upperExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1064_valid
  · exact exp1064_valid
  · exact exp1064_valid
theorem data31262_center_valid : ∀ j, (data31262.centerExp j).Valid := by
  intro j
  fin_cases j
  · exact exp1056_valid
  · exact exp1056_valid
  · exact exp1048_valid
theorem margin31262 : 0 < data31262.apexRefinedMargin 0 := by decide +kernel
theorem conclusion31262 {q : EdgeTriple} (hq : q ∈ box31262.region) :
    ApexLeafConclusion 0 q := by
  apply apexLeafConclusion_of_positive
  exact data31262.apexRefined_positive 0
    data31262_lower_valid data31262_upper_valid data31262_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin31262 hq

end SparseLowerTail.Section05.ApexReplay.F1
