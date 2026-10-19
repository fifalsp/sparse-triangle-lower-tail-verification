import SparseLowerTail.Section05.CoverS1HornerTaylor
import SparseLowerTail.Numerics.CachedPolynomial

/-! Pre-rounded constants for repeated S1 Taylor evaluation. Each conversion is
checked once; compositional validity proofs reuse those checked conversions. -/
namespace SparseLowerTail.Section05
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000


def s1CachedNode0 : CachedPolynomialExpr 9 := .rational (8639019645839429/9007199254740992 : ℚ) ⟨1105794514667446912,1105794514667446912⟩

theorem s1CachedNode0_valid : s1CachedNode0.Valid := by decide +kernel

def s1CachedNode1 : CachedPolynomialExpr 9 := .var 3

theorem s1CachedNode1_valid : s1CachedNode1.Valid := True.intro

def s1CachedNode2 : CachedPolynomialExpr 9 := .var 4

theorem s1CachedNode2_valid : s1CachedNode2.Valid := True.intro

def s1CachedNode3 : CachedPolynomialExpr 9 := .add s1CachedNode1 s1CachedNode2

theorem s1CachedNode3_valid : s1CachedNode3.Valid := ⟨s1CachedNode1_valid,s1CachedNode2_valid⟩

def s1CachedNode4 : CachedPolynomialExpr 9 := .var 5

theorem s1CachedNode4_valid : s1CachedNode4.Valid := True.intro

def s1CachedNode5 : CachedPolynomialExpr 9 := .add s1CachedNode3 s1CachedNode4

theorem s1CachedNode5_valid : s1CachedNode5.Valid := ⟨s1CachedNode3_valid,s1CachedNode4_valid⟩

def s1CachedNode6 : CachedPolynomialExpr 9 := .rational (1/3 : ℚ) ⟨384307168202282325,384307168202282326⟩

theorem s1CachedNode6_valid : s1CachedNode6.Valid := by decide +kernel

def s1CachedNode7 : CachedPolynomialExpr 9 := .mul s1CachedNode5 s1CachedNode6

theorem s1CachedNode7_valid : s1CachedNode7.Valid := ⟨s1CachedNode5_valid,s1CachedNode6_valid⟩

def s1CachedNode8 : CachedPolynomialExpr 9 := .rational (7872292148643627/36028797018963968 : ℚ) ⟨251913348756596064,251913348756596064⟩

theorem s1CachedNode8_valid : s1CachedNode8.Valid := by decide +kernel

def s1CachedNode9 : CachedPolynomialExpr 9 := .neg s1CachedNode8

theorem s1CachedNode9_valid : s1CachedNode9.Valid := s1CachedNode8_valid

def s1CachedNode10 : CachedPolynomialExpr 9 := .add s1CachedNode7 s1CachedNode9

theorem s1CachedNode10_valid : s1CachedNode10.Valid := ⟨s1CachedNode7_valid,s1CachedNode9_valid⟩

def s1CachedNode11 : CachedPolynomialExpr 9 := .mul s1CachedNode0 s1CachedNode10

theorem s1CachedNode11_valid : s1CachedNode11.Valid := ⟨s1CachedNode0_valid,s1CachedNode10_valid⟩

def s1CachedNode12 : CachedPolynomialExpr 9 := .rational (-2657272677596523/562949953421312 : ℚ) ⟨-5442094443717679104,-5442094443717679104⟩

theorem s1CachedNode12_valid : s1CachedNode12.Valid := by decide +kernel

def s1CachedNode13 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode2

theorem s1CachedNode13_valid : s1CachedNode13.Valid := ⟨s1CachedNode1_valid,s1CachedNode2_valid⟩

def s1CachedNode14 : CachedPolynomialExpr 9 := .mul s1CachedNode13 s1CachedNode4

theorem s1CachedNode14_valid : s1CachedNode14.Valid := ⟨s1CachedNode13_valid,s1CachedNode4_valid⟩

def s1CachedNode15 : CachedPolynomialExpr 9 := .var 6

theorem s1CachedNode15_valid : s1CachedNode15.Valid := True.intro

def s1CachedNode16 : CachedPolynomialExpr 9 := .neg s1CachedNode15

theorem s1CachedNode16_valid : s1CachedNode16.Valid := s1CachedNode15_valid

def s1CachedNode17 : CachedPolynomialExpr 9 := .add s1CachedNode14 s1CachedNode16

theorem s1CachedNode17_valid : s1CachedNode17.Valid := ⟨s1CachedNode14_valid,s1CachedNode16_valid⟩

def s1CachedNode18 : CachedPolynomialExpr 9 := .mul s1CachedNode12 s1CachedNode17

theorem s1CachedNode18_valid : s1CachedNode18.Valid := ⟨s1CachedNode12_valid,s1CachedNode17_valid⟩

def s1CachedNode19 : CachedPolynomialExpr 9 := .rational (140737488299033/140737488355328 : ℚ) ⟨1152921504145678336,1152921504145678336⟩

theorem s1CachedNode19_valid : s1CachedNode19.Valid := by decide +kernel

def s1CachedNode20 : CachedPolynomialExpr 9 := .var 0

theorem s1CachedNode20_valid : s1CachedNode20.Valid := True.intro

def s1CachedNode21 : CachedPolynomialExpr 9 := .neg s1CachedNode20

theorem s1CachedNode21_valid : s1CachedNode21.Valid := s1CachedNode20_valid

def s1CachedNode22 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode21

theorem s1CachedNode22_valid : s1CachedNode22.Valid := ⟨s1CachedNode1_valid,s1CachedNode21_valid⟩

def s1CachedNode23 : CachedPolynomialExpr 9 := .neg s1CachedNode1

theorem s1CachedNode23_valid : s1CachedNode23.Valid := s1CachedNode1_valid

def s1CachedNode24 : CachedPolynomialExpr 9 := .add s1CachedNode22 s1CachedNode23

theorem s1CachedNode24_valid : s1CachedNode24.Valid := ⟨s1CachedNode22_valid,s1CachedNode23_valid⟩

def s1CachedNode25 : CachedPolynomialExpr 9 := .rational (1/1 : ℚ) ⟨1152921504606846976,1152921504606846976⟩

theorem s1CachedNode25_valid : s1CachedNode25.Valid := by decide +kernel

def s1CachedNode26 : CachedPolynomialExpr 9 := .add s1CachedNode24 s1CachedNode25

theorem s1CachedNode26_valid : s1CachedNode26.Valid := ⟨s1CachedNode24_valid,s1CachedNode25_valid⟩

def s1CachedNode27 : CachedPolynomialExpr 9 := .var 1

theorem s1CachedNode27_valid : s1CachedNode27.Valid := True.intro

def s1CachedNode28 : CachedPolynomialExpr 9 := .neg s1CachedNode27

theorem s1CachedNode28_valid : s1CachedNode28.Valid := s1CachedNode27_valid

def s1CachedNode29 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode28

theorem s1CachedNode29_valid : s1CachedNode29.Valid := ⟨s1CachedNode2_valid,s1CachedNode28_valid⟩

def s1CachedNode30 : CachedPolynomialExpr 9 := .neg s1CachedNode2

theorem s1CachedNode30_valid : s1CachedNode30.Valid := s1CachedNode2_valid

def s1CachedNode31 : CachedPolynomialExpr 9 := .add s1CachedNode29 s1CachedNode30

theorem s1CachedNode31_valid : s1CachedNode31.Valid := ⟨s1CachedNode29_valid,s1CachedNode30_valid⟩

def s1CachedNode32 : CachedPolynomialExpr 9 := .add s1CachedNode31 s1CachedNode25

theorem s1CachedNode32_valid : s1CachedNode32.Valid := ⟨s1CachedNode31_valid,s1CachedNode25_valid⟩

def s1CachedNode33 : CachedPolynomialExpr 9 := .add s1CachedNode26 s1CachedNode32

theorem s1CachedNode33_valid : s1CachedNode33.Valid := ⟨s1CachedNode26_valid,s1CachedNode32_valid⟩

def s1CachedNode34 : CachedPolynomialExpr 9 := .var 2

theorem s1CachedNode34_valid : s1CachedNode34.Valid := True.intro

def s1CachedNode35 : CachedPolynomialExpr 9 := .neg s1CachedNode34

theorem s1CachedNode35_valid : s1CachedNode35.Valid := s1CachedNode34_valid

def s1CachedNode36 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode35

theorem s1CachedNode36_valid : s1CachedNode36.Valid := ⟨s1CachedNode4_valid,s1CachedNode35_valid⟩

def s1CachedNode37 : CachedPolynomialExpr 9 := .neg s1CachedNode4

theorem s1CachedNode37_valid : s1CachedNode37.Valid := s1CachedNode4_valid

def s1CachedNode38 : CachedPolynomialExpr 9 := .add s1CachedNode36 s1CachedNode37

theorem s1CachedNode38_valid : s1CachedNode38.Valid := ⟨s1CachedNode36_valid,s1CachedNode37_valid⟩

def s1CachedNode39 : CachedPolynomialExpr 9 := .add s1CachedNode38 s1CachedNode25

theorem s1CachedNode39_valid : s1CachedNode39.Valid := ⟨s1CachedNode38_valid,s1CachedNode25_valid⟩

def s1CachedNode40 : CachedPolynomialExpr 9 := .add s1CachedNode33 s1CachedNode39

theorem s1CachedNode40_valid : s1CachedNode40.Valid := ⟨s1CachedNode33_valid,s1CachedNode39_valid⟩

def s1CachedNode41 : CachedPolynomialExpr 9 := .mul s1CachedNode40 s1CachedNode6

theorem s1CachedNode41_valid : s1CachedNode41.Valid := ⟨s1CachedNode40_valid,s1CachedNode6_valid⟩

def s1CachedNode42 : CachedPolynomialExpr 9 := .rational (8304637712871195/18014398509481984 : ℚ) ⟨531496813623756480,531496813623756480⟩

theorem s1CachedNode42_valid : s1CachedNode42.Valid := by decide +kernel

def s1CachedNode43 : CachedPolynomialExpr 9 := .neg s1CachedNode42

theorem s1CachedNode43_valid : s1CachedNode43.Valid := s1CachedNode42_valid

def s1CachedNode44 : CachedPolynomialExpr 9 := .add s1CachedNode41 s1CachedNode43

theorem s1CachedNode44_valid : s1CachedNode44.Valid := ⟨s1CachedNode41_valid,s1CachedNode43_valid⟩

def s1CachedNode45 : CachedPolynomialExpr 9 := .mul s1CachedNode19 s1CachedNode44

theorem s1CachedNode45_valid : s1CachedNode45.Valid := ⟨s1CachedNode19_valid,s1CachedNode44_valid⟩

def s1CachedNode46 : CachedPolynomialExpr 9 := .rational (-7541973450629039/36893488147419103232 : ℚ) ⟨-235686670332158,-235686670332157⟩

theorem s1CachedNode46_valid : s1CachedNode46.Valid := by decide +kernel

def s1CachedNode47 : CachedPolynomialExpr 9 := .var 8

theorem s1CachedNode47_valid : s1CachedNode47.Valid := True.intro

def s1CachedNode48 : CachedPolynomialExpr 9 := .mul s1CachedNode47 s1CachedNode2

theorem s1CachedNode48_valid : s1CachedNode48.Valid := ⟨s1CachedNode47_valid,s1CachedNode2_valid⟩

def s1CachedNode49 : CachedPolynomialExpr 9 := .mul s1CachedNode48 s1CachedNode4

theorem s1CachedNode49_valid : s1CachedNode49.Valid := ⟨s1CachedNode48_valid,s1CachedNode4_valid⟩

def s1CachedNode50 : CachedPolynomialExpr 9 := .add s1CachedNode21 s1CachedNode49

theorem s1CachedNode50_valid : s1CachedNode50.Valid := ⟨s1CachedNode21_valid,s1CachedNode49_valid⟩

def s1CachedNode51 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode50

theorem s1CachedNode51_valid : s1CachedNode51.Valid := ⟨s1CachedNode25_valid,s1CachedNode50_valid⟩

def s1CachedNode52 : CachedPolynomialExpr 9 := .mul s1CachedNode47 s1CachedNode4

theorem s1CachedNode52_valid : s1CachedNode52.Valid := ⟨s1CachedNode47_valid,s1CachedNode4_valid⟩

def s1CachedNode53 : CachedPolynomialExpr 9 := .mul s1CachedNode52 s1CachedNode1

theorem s1CachedNode53_valid : s1CachedNode53.Valid := ⟨s1CachedNode52_valid,s1CachedNode1_valid⟩

def s1CachedNode54 : CachedPolynomialExpr 9 := .add s1CachedNode28 s1CachedNode53

theorem s1CachedNode54_valid : s1CachedNode54.Valid := ⟨s1CachedNode28_valid,s1CachedNode53_valid⟩

def s1CachedNode55 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode54

theorem s1CachedNode55_valid : s1CachedNode55.Valid := ⟨s1CachedNode25_valid,s1CachedNode54_valid⟩

def s1CachedNode56 : CachedPolynomialExpr 9 := .add s1CachedNode51 s1CachedNode55

theorem s1CachedNode56_valid : s1CachedNode56.Valid := ⟨s1CachedNode51_valid,s1CachedNode55_valid⟩

def s1CachedNode57 : CachedPolynomialExpr 9 := .mul s1CachedNode47 s1CachedNode1

theorem s1CachedNode57_valid : s1CachedNode57.Valid := ⟨s1CachedNode47_valid,s1CachedNode1_valid⟩

def s1CachedNode58 : CachedPolynomialExpr 9 := .mul s1CachedNode57 s1CachedNode2

theorem s1CachedNode58_valid : s1CachedNode58.Valid := ⟨s1CachedNode57_valid,s1CachedNode2_valid⟩

def s1CachedNode59 : CachedPolynomialExpr 9 := .add s1CachedNode35 s1CachedNode58

theorem s1CachedNode59_valid : s1CachedNode59.Valid := ⟨s1CachedNode35_valid,s1CachedNode58_valid⟩

def s1CachedNode60 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode59

theorem s1CachedNode60_valid : s1CachedNode60.Valid := ⟨s1CachedNode25_valid,s1CachedNode59_valid⟩

def s1CachedNode61 : CachedPolynomialExpr 9 := .add s1CachedNode56 s1CachedNode60

theorem s1CachedNode61_valid : s1CachedNode61.Valid := ⟨s1CachedNode56_valid,s1CachedNode60_valid⟩

def s1CachedNode62 : CachedPolynomialExpr 9 := .mul s1CachedNode61 s1CachedNode6

theorem s1CachedNode62_valid : s1CachedNode62.Valid := ⟨s1CachedNode61_valid,s1CachedNode6_valid⟩

def s1CachedNode63 : CachedPolynomialExpr 9 := .mul s1CachedNode46 s1CachedNode62

theorem s1CachedNode63_valid : s1CachedNode63.Valid := ⟨s1CachedNode46_valid,s1CachedNode62_valid⟩

def s1CachedNode64 : CachedPolynomialExpr 9 := .rational (-8604084221028639/72057594037927936 : ℚ) ⟨-137665347536458224,-137665347536458224⟩

theorem s1CachedNode64_valid : s1CachedNode64.Valid := by decide +kernel

def s1CachedNode65 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode50

theorem s1CachedNode65_valid : s1CachedNode65.Valid := ⟨s1CachedNode1_valid,s1CachedNode50_valid⟩

def s1CachedNode66 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode54

theorem s1CachedNode66_valid : s1CachedNode66.Valid := ⟨s1CachedNode2_valid,s1CachedNode54_valid⟩

def s1CachedNode67 : CachedPolynomialExpr 9 := .add s1CachedNode65 s1CachedNode66

theorem s1CachedNode67_valid : s1CachedNode67.Valid := ⟨s1CachedNode65_valid,s1CachedNode66_valid⟩

def s1CachedNode68 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode59

theorem s1CachedNode68_valid : s1CachedNode68.Valid := ⟨s1CachedNode4_valid,s1CachedNode59_valid⟩

def s1CachedNode69 : CachedPolynomialExpr 9 := .add s1CachedNode67 s1CachedNode68

theorem s1CachedNode69_valid : s1CachedNode69.Valid := ⟨s1CachedNode67_valid,s1CachedNode68_valid⟩

def s1CachedNode70 : CachedPolynomialExpr 9 := .mul s1CachedNode69 s1CachedNode6

theorem s1CachedNode70_valid : s1CachedNode70.Valid := ⟨s1CachedNode69_valid,s1CachedNode6_valid⟩

def s1CachedNode71 : CachedPolynomialExpr 9 := .mul s1CachedNode64 s1CachedNode70

theorem s1CachedNode71_valid : s1CachedNode71.Valid := ⟨s1CachedNode64_valid,s1CachedNode70_valid⟩

def s1CachedNode72 : CachedPolynomialExpr 9 := .rational (1019507261509151/1125899906842624 : ℚ) ⟨1043975435785370624,1043975435785370624⟩

theorem s1CachedNode72_valid : s1CachedNode72.Valid := by decide +kernel

def s1CachedNode73 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode1

theorem s1CachedNode73_valid : s1CachedNode73.Valid := ⟨s1CachedNode25_valid,s1CachedNode1_valid⟩

def s1CachedNode74 : CachedPolynomialExpr 9 := .mul s1CachedNode73 s1CachedNode1

theorem s1CachedNode74_valid : s1CachedNode74.Valid := ⟨s1CachedNode73_valid,s1CachedNode1_valid⟩

def s1CachedNode75 : CachedPolynomialExpr 9 := .mul s1CachedNode74 s1CachedNode50

theorem s1CachedNode75_valid : s1CachedNode75.Valid := ⟨s1CachedNode74_valid,s1CachedNode50_valid⟩

def s1CachedNode76 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode2

theorem s1CachedNode76_valid : s1CachedNode76.Valid := ⟨s1CachedNode25_valid,s1CachedNode2_valid⟩

def s1CachedNode77 : CachedPolynomialExpr 9 := .mul s1CachedNode76 s1CachedNode2

theorem s1CachedNode77_valid : s1CachedNode77.Valid := ⟨s1CachedNode76_valid,s1CachedNode2_valid⟩

def s1CachedNode78 : CachedPolynomialExpr 9 := .mul s1CachedNode77 s1CachedNode54

theorem s1CachedNode78_valid : s1CachedNode78.Valid := ⟨s1CachedNode77_valid,s1CachedNode54_valid⟩

def s1CachedNode79 : CachedPolynomialExpr 9 := .add s1CachedNode75 s1CachedNode78

theorem s1CachedNode79_valid : s1CachedNode79.Valid := ⟨s1CachedNode75_valid,s1CachedNode78_valid⟩

def s1CachedNode80 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode4

theorem s1CachedNode80_valid : s1CachedNode80.Valid := ⟨s1CachedNode25_valid,s1CachedNode4_valid⟩

def s1CachedNode81 : CachedPolynomialExpr 9 := .mul s1CachedNode80 s1CachedNode4

theorem s1CachedNode81_valid : s1CachedNode81.Valid := ⟨s1CachedNode80_valid,s1CachedNode4_valid⟩

def s1CachedNode82 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode59

theorem s1CachedNode82_valid : s1CachedNode82.Valid := ⟨s1CachedNode81_valid,s1CachedNode59_valid⟩

def s1CachedNode83 : CachedPolynomialExpr 9 := .add s1CachedNode79 s1CachedNode82

theorem s1CachedNode83_valid : s1CachedNode83.Valid := ⟨s1CachedNode79_valid,s1CachedNode82_valid⟩

def s1CachedNode84 : CachedPolynomialExpr 9 := .mul s1CachedNode83 s1CachedNode6

theorem s1CachedNode84_valid : s1CachedNode84.Valid := ⟨s1CachedNode83_valid,s1CachedNode6_valid⟩

def s1CachedNode85 : CachedPolynomialExpr 9 := .mul s1CachedNode72 s1CachedNode84

theorem s1CachedNode85_valid : s1CachedNode85.Valid := ⟨s1CachedNode72_valid,s1CachedNode84_valid⟩

def s1CachedNode86 : CachedPolynomialExpr 9 := .rational (-7199522257880297/9007199254740992 : ℚ) ⟨-921538849008678016,-921538849008678016⟩

theorem s1CachedNode86_valid : s1CachedNode86.Valid := by decide +kernel

def s1CachedNode87 : CachedPolynomialExpr 9 := .mul s1CachedNode74 s1CachedNode1

theorem s1CachedNode87_valid : s1CachedNode87.Valid := ⟨s1CachedNode74_valid,s1CachedNode1_valid⟩

def s1CachedNode88 : CachedPolynomialExpr 9 := .mul s1CachedNode87 s1CachedNode50

theorem s1CachedNode88_valid : s1CachedNode88.Valid := ⟨s1CachedNode87_valid,s1CachedNode50_valid⟩

def s1CachedNode89 : CachedPolynomialExpr 9 := .mul s1CachedNode77 s1CachedNode2

theorem s1CachedNode89_valid : s1CachedNode89.Valid := ⟨s1CachedNode77_valid,s1CachedNode2_valid⟩

def s1CachedNode90 : CachedPolynomialExpr 9 := .mul s1CachedNode89 s1CachedNode54

theorem s1CachedNode90_valid : s1CachedNode90.Valid := ⟨s1CachedNode89_valid,s1CachedNode54_valid⟩

def s1CachedNode91 : CachedPolynomialExpr 9 := .add s1CachedNode88 s1CachedNode90

theorem s1CachedNode91_valid : s1CachedNode91.Valid := ⟨s1CachedNode88_valid,s1CachedNode90_valid⟩

def s1CachedNode92 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode4

theorem s1CachedNode92_valid : s1CachedNode92.Valid := ⟨s1CachedNode81_valid,s1CachedNode4_valid⟩

def s1CachedNode93 : CachedPolynomialExpr 9 := .mul s1CachedNode92 s1CachedNode59

theorem s1CachedNode93_valid : s1CachedNode93.Valid := ⟨s1CachedNode92_valid,s1CachedNode59_valid⟩

def s1CachedNode94 : CachedPolynomialExpr 9 := .add s1CachedNode91 s1CachedNode93

theorem s1CachedNode94_valid : s1CachedNode94.Valid := ⟨s1CachedNode91_valid,s1CachedNode93_valid⟩

def s1CachedNode95 : CachedPolynomialExpr 9 := .mul s1CachedNode94 s1CachedNode6

theorem s1CachedNode95_valid : s1CachedNode95.Valid := ⟨s1CachedNode94_valid,s1CachedNode6_valid⟩

def s1CachedNode96 : CachedPolynomialExpr 9 := .mul s1CachedNode86 s1CachedNode95

theorem s1CachedNode96_valid : s1CachedNode96.Valid := ⟨s1CachedNode86_valid,s1CachedNode95_valid⟩

def s1CachedNode97 : CachedPolynomialExpr 9 := .rational (8774057038934945/72057594037927936 : ℚ) ⟨140384912622959120,140384912622959120⟩

theorem s1CachedNode97_valid : s1CachedNode97.Valid := by decide +kernel

def s1CachedNode98 : CachedPolynomialExpr 9 := .mul s1CachedNode22 s1CachedNode50

theorem s1CachedNode98_valid : s1CachedNode98.Valid := ⟨s1CachedNode22_valid,s1CachedNode50_valid⟩

def s1CachedNode99 : CachedPolynomialExpr 9 := .mul s1CachedNode29 s1CachedNode54

theorem s1CachedNode99_valid : s1CachedNode99.Valid := ⟨s1CachedNode29_valid,s1CachedNode54_valid⟩

def s1CachedNode100 : CachedPolynomialExpr 9 := .add s1CachedNode98 s1CachedNode99

theorem s1CachedNode100_valid : s1CachedNode100.Valid := ⟨s1CachedNode98_valid,s1CachedNode99_valid⟩

def s1CachedNode101 : CachedPolynomialExpr 9 := .mul s1CachedNode36 s1CachedNode59

theorem s1CachedNode101_valid : s1CachedNode101.Valid := ⟨s1CachedNode36_valid,s1CachedNode59_valid⟩

def s1CachedNode102 : CachedPolynomialExpr 9 := .add s1CachedNode100 s1CachedNode101

theorem s1CachedNode102_valid : s1CachedNode102.Valid := ⟨s1CachedNode100_valid,s1CachedNode101_valid⟩

def s1CachedNode103 : CachedPolynomialExpr 9 := .mul s1CachedNode102 s1CachedNode6

theorem s1CachedNode103_valid : s1CachedNode103.Valid := ⟨s1CachedNode102_valid,s1CachedNode6_valid⟩

def s1CachedNode104 : CachedPolynomialExpr 9 := .mul s1CachedNode97 s1CachedNode103

theorem s1CachedNode104_valid : s1CachedNode104.Valid := ⟨s1CachedNode97_valid,s1CachedNode103_valid⟩

def s1CachedNode105 : CachedPolynomialExpr 9 := .rational (-2521529215217977/18014398509481984 : ℚ) ⟨-161377869773950528,-161377869773950528⟩

theorem s1CachedNode105_valid : s1CachedNode105.Valid := by decide +kernel

def s1CachedNode106 : CachedPolynomialExpr 9 := .rational (2/1 : ℚ) ⟨2305843009213693952,2305843009213693952⟩

theorem s1CachedNode106_valid : s1CachedNode106.Valid := by decide +kernel

def s1CachedNode107 : CachedPolynomialExpr 9 := .mul s1CachedNode106 s1CachedNode2

theorem s1CachedNode107_valid : s1CachedNode107.Valid := ⟨s1CachedNode106_valid,s1CachedNode2_valid⟩

def s1CachedNode108 : CachedPolynomialExpr 9 := .neg s1CachedNode107

theorem s1CachedNode108_valid : s1CachedNode108.Valid := s1CachedNode107_valid

def s1CachedNode109 : CachedPolynomialExpr 9 := .add s1CachedNode29 s1CachedNode108

theorem s1CachedNode109_valid : s1CachedNode109.Valid := ⟨s1CachedNode29_valid,s1CachedNode108_valid⟩

def s1CachedNode110 : CachedPolynomialExpr 9 := .add s1CachedNode109 s1CachedNode106

theorem s1CachedNode110_valid : s1CachedNode110.Valid := ⟨s1CachedNode109_valid,s1CachedNode106_valid⟩

def s1CachedNode111 : CachedPolynomialExpr 9 := .mul s1CachedNode106 s1CachedNode4

theorem s1CachedNode111_valid : s1CachedNode111.Valid := ⟨s1CachedNode106_valid,s1CachedNode4_valid⟩

def s1CachedNode112 : CachedPolynomialExpr 9 := .neg s1CachedNode111

theorem s1CachedNode112_valid : s1CachedNode112.Valid := s1CachedNode111_valid

def s1CachedNode113 : CachedPolynomialExpr 9 := .add s1CachedNode36 s1CachedNode112

theorem s1CachedNode113_valid : s1CachedNode113.Valid := ⟨s1CachedNode36_valid,s1CachedNode112_valid⟩

def s1CachedNode114 : CachedPolynomialExpr 9 := .add s1CachedNode113 s1CachedNode106

theorem s1CachedNode114_valid : s1CachedNode114.Valid := ⟨s1CachedNode113_valid,s1CachedNode106_valid⟩

def s1CachedNode115 : CachedPolynomialExpr 9 := .add s1CachedNode110 s1CachedNode114

theorem s1CachedNode115_valid : s1CachedNode115.Valid := ⟨s1CachedNode110_valid,s1CachedNode114_valid⟩

def s1CachedNode116 : CachedPolynomialExpr 9 := .add s1CachedNode25 s1CachedNode42

theorem s1CachedNode116_valid : s1CachedNode116.Valid := ⟨s1CachedNode25_valid,s1CachedNode42_valid⟩

def s1CachedNode117 : CachedPolynomialExpr 9 := .add s1CachedNode116 s1CachedNode9

theorem s1CachedNode117_valid : s1CachedNode117.Valid := ⟨s1CachedNode116_valid,s1CachedNode9_valid⟩

def s1CachedNode118 : CachedPolynomialExpr 9 := .mul s1CachedNode106 s1CachedNode117

theorem s1CachedNode118_valid : s1CachedNode118.Valid := ⟨s1CachedNode106_valid,s1CachedNode117_valid⟩

def s1CachedNode119 : CachedPolynomialExpr 9 := .neg s1CachedNode118

theorem s1CachedNode119_valid : s1CachedNode119.Valid := s1CachedNode118_valid

def s1CachedNode120 : CachedPolynomialExpr 9 := .add s1CachedNode115 s1CachedNode119

theorem s1CachedNode120_valid : s1CachedNode120.Valid := ⟨s1CachedNode115_valid,s1CachedNode119_valid⟩

def s1CachedNode121 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode120

theorem s1CachedNode121_valid : s1CachedNode121.Valid := ⟨s1CachedNode1_valid,s1CachedNode120_valid⟩

def s1CachedNode122 : CachedPolynomialExpr 9 := .mul s1CachedNode106 s1CachedNode1

theorem s1CachedNode122_valid : s1CachedNode122.Valid := ⟨s1CachedNode106_valid,s1CachedNode1_valid⟩

def s1CachedNode123 : CachedPolynomialExpr 9 := .neg s1CachedNode122

theorem s1CachedNode123_valid : s1CachedNode123.Valid := s1CachedNode122_valid

def s1CachedNode124 : CachedPolynomialExpr 9 := .add s1CachedNode22 s1CachedNode123

theorem s1CachedNode124_valid : s1CachedNode124.Valid := ⟨s1CachedNode22_valid,s1CachedNode123_valid⟩

def s1CachedNode125 : CachedPolynomialExpr 9 := .add s1CachedNode124 s1CachedNode106

theorem s1CachedNode125_valid : s1CachedNode125.Valid := ⟨s1CachedNode124_valid,s1CachedNode106_valid⟩

def s1CachedNode126 : CachedPolynomialExpr 9 := .add s1CachedNode114 s1CachedNode125

theorem s1CachedNode126_valid : s1CachedNode126.Valid := ⟨s1CachedNode114_valid,s1CachedNode125_valid⟩

def s1CachedNode127 : CachedPolynomialExpr 9 := .add s1CachedNode126 s1CachedNode119

theorem s1CachedNode127_valid : s1CachedNode127.Valid := ⟨s1CachedNode126_valid,s1CachedNode119_valid⟩

def s1CachedNode128 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode127

theorem s1CachedNode128_valid : s1CachedNode128.Valid := ⟨s1CachedNode2_valid,s1CachedNode127_valid⟩

def s1CachedNode129 : CachedPolynomialExpr 9 := .add s1CachedNode121 s1CachedNode128

theorem s1CachedNode129_valid : s1CachedNode129.Valid := ⟨s1CachedNode121_valid,s1CachedNode128_valid⟩

def s1CachedNode130 : CachedPolynomialExpr 9 := .add s1CachedNode125 s1CachedNode110

theorem s1CachedNode130_valid : s1CachedNode130.Valid := ⟨s1CachedNode125_valid,s1CachedNode110_valid⟩

def s1CachedNode131 : CachedPolynomialExpr 9 := .add s1CachedNode130 s1CachedNode119

theorem s1CachedNode131_valid : s1CachedNode131.Valid := ⟨s1CachedNode130_valid,s1CachedNode119_valid⟩

def s1CachedNode132 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode131

theorem s1CachedNode132_valid : s1CachedNode132.Valid := ⟨s1CachedNode4_valid,s1CachedNode131_valid⟩

def s1CachedNode133 : CachedPolynomialExpr 9 := .add s1CachedNode129 s1CachedNode132

theorem s1CachedNode133_valid : s1CachedNode133.Valid := ⟨s1CachedNode129_valid,s1CachedNode132_valid⟩

def s1CachedNode134 : CachedPolynomialExpr 9 := .mul s1CachedNode133 s1CachedNode6

theorem s1CachedNode134_valid : s1CachedNode134.Valid := ⟨s1CachedNode133_valid,s1CachedNode6_valid⟩

def s1CachedNode135 : CachedPolynomialExpr 9 := .mul s1CachedNode105 s1CachedNode134

theorem s1CachedNode135_valid : s1CachedNode135.Valid := ⟨s1CachedNode105_valid,s1CachedNode134_valid⟩

def s1CachedNode136 : CachedPolynomialExpr 9 := .rational (7097966112403971/18014398509481984 : ℚ) ⟨454269831193854144,454269831193854144⟩

theorem s1CachedNode136_valid : s1CachedNode136.Valid := by decide +kernel

def s1CachedNode137 : CachedPolynomialExpr 9 := .mul s1CachedNode87 s1CachedNode120

theorem s1CachedNode137_valid : s1CachedNode137.Valid := ⟨s1CachedNode87_valid,s1CachedNode120_valid⟩

def s1CachedNode138 : CachedPolynomialExpr 9 := .mul s1CachedNode89 s1CachedNode127

theorem s1CachedNode138_valid : s1CachedNode138.Valid := ⟨s1CachedNode89_valid,s1CachedNode127_valid⟩

def s1CachedNode139 : CachedPolynomialExpr 9 := .add s1CachedNode137 s1CachedNode138

theorem s1CachedNode139_valid : s1CachedNode139.Valid := ⟨s1CachedNode137_valid,s1CachedNode138_valid⟩

def s1CachedNode140 : CachedPolynomialExpr 9 := .mul s1CachedNode92 s1CachedNode131

theorem s1CachedNode140_valid : s1CachedNode140.Valid := ⟨s1CachedNode92_valid,s1CachedNode131_valid⟩

def s1CachedNode141 : CachedPolynomialExpr 9 := .add s1CachedNode139 s1CachedNode140

theorem s1CachedNode141_valid : s1CachedNode141.Valid := ⟨s1CachedNode139_valid,s1CachedNode140_valid⟩

def s1CachedNode142 : CachedPolynomialExpr 9 := .mul s1CachedNode141 s1CachedNode6

theorem s1CachedNode142_valid : s1CachedNode142.Valid := ⟨s1CachedNode141_valid,s1CachedNode6_valid⟩

def s1CachedNode143 : CachedPolynomialExpr 9 := .mul s1CachedNode136 s1CachedNode142

theorem s1CachedNode143_valid : s1CachedNode143.Valid := ⟨s1CachedNode136_valid,s1CachedNode142_valid⟩

def s1CachedNode144 : CachedPolynomialExpr 9 := .rational (-6881924343606227/9007199254740992 : ℚ) ⟨-880886315981597056,-880886315981597056⟩

theorem s1CachedNode144_valid : s1CachedNode144.Valid := by decide +kernel

def s1CachedNode145 : CachedPolynomialExpr 9 := .mul s1CachedNode87 s1CachedNode1

theorem s1CachedNode145_valid : s1CachedNode145.Valid := ⟨s1CachedNode87_valid,s1CachedNode1_valid⟩

def s1CachedNode146 : CachedPolynomialExpr 9 := .mul s1CachedNode145 s1CachedNode120

theorem s1CachedNode146_valid : s1CachedNode146.Valid := ⟨s1CachedNode145_valid,s1CachedNode120_valid⟩

def s1CachedNode147 : CachedPolynomialExpr 9 := .mul s1CachedNode89 s1CachedNode2

theorem s1CachedNode147_valid : s1CachedNode147.Valid := ⟨s1CachedNode89_valid,s1CachedNode2_valid⟩

def s1CachedNode148 : CachedPolynomialExpr 9 := .mul s1CachedNode147 s1CachedNode127

theorem s1CachedNode148_valid : s1CachedNode148.Valid := ⟨s1CachedNode147_valid,s1CachedNode127_valid⟩

def s1CachedNode149 : CachedPolynomialExpr 9 := .add s1CachedNode146 s1CachedNode148

theorem s1CachedNode149_valid : s1CachedNode149.Valid := ⟨s1CachedNode146_valid,s1CachedNode148_valid⟩

def s1CachedNode150 : CachedPolynomialExpr 9 := .mul s1CachedNode92 s1CachedNode4

theorem s1CachedNode150_valid : s1CachedNode150.Valid := ⟨s1CachedNode92_valid,s1CachedNode4_valid⟩

def s1CachedNode151 : CachedPolynomialExpr 9 := .mul s1CachedNode150 s1CachedNode131

theorem s1CachedNode151_valid : s1CachedNode151.Valid := ⟨s1CachedNode150_valid,s1CachedNode131_valid⟩

def s1CachedNode152 : CachedPolynomialExpr 9 := .add s1CachedNode149 s1CachedNode151

theorem s1CachedNode152_valid : s1CachedNode152.Valid := ⟨s1CachedNode149_valid,s1CachedNode151_valid⟩

def s1CachedNode153 : CachedPolynomialExpr 9 := .mul s1CachedNode152 s1CachedNode6

theorem s1CachedNode153_valid : s1CachedNode153.Valid := ⟨s1CachedNode152_valid,s1CachedNode6_valid⟩

def s1CachedNode154 : CachedPolynomialExpr 9 := .mul s1CachedNode144 s1CachedNode153

theorem s1CachedNode154_valid : s1CachedNode154.Valid := ⟨s1CachedNode144_valid,s1CachedNode153_valid⟩

def s1CachedNode155 : CachedPolynomialExpr 9 := .rational (3354424007516313/4503599627370496 : ℚ) ⟨858732545924176128,858732545924176128⟩

theorem s1CachedNode155_valid : s1CachedNode155.Valid := by decide +kernel

def s1CachedNode156 : CachedPolynomialExpr 9 := .mul s1CachedNode22 s1CachedNode120

theorem s1CachedNode156_valid : s1CachedNode156.Valid := ⟨s1CachedNode22_valid,s1CachedNode120_valid⟩

def s1CachedNode157 : CachedPolynomialExpr 9 := .mul s1CachedNode29 s1CachedNode127

theorem s1CachedNode157_valid : s1CachedNode157.Valid := ⟨s1CachedNode29_valid,s1CachedNode127_valid⟩

def s1CachedNode158 : CachedPolynomialExpr 9 := .add s1CachedNode156 s1CachedNode157

theorem s1CachedNode158_valid : s1CachedNode158.Valid := ⟨s1CachedNode156_valid,s1CachedNode157_valid⟩

def s1CachedNode159 : CachedPolynomialExpr 9 := .mul s1CachedNode36 s1CachedNode131

theorem s1CachedNode159_valid : s1CachedNode159.Valid := ⟨s1CachedNode36_valid,s1CachedNode131_valid⟩

def s1CachedNode160 : CachedPolynomialExpr 9 := .add s1CachedNode158 s1CachedNode159

theorem s1CachedNode160_valid : s1CachedNode160.Valid := ⟨s1CachedNode158_valid,s1CachedNode159_valid⟩

def s1CachedNode161 : CachedPolynomialExpr 9 := .mul s1CachedNode160 s1CachedNode6

theorem s1CachedNode161_valid : s1CachedNode161.Valid := ⟨s1CachedNode160_valid,s1CachedNode6_valid⟩

def s1CachedNode162 : CachedPolynomialExpr 9 := .mul s1CachedNode155 s1CachedNode161

theorem s1CachedNode162_valid : s1CachedNode162.Valid := ⟨s1CachedNode155_valid,s1CachedNode161_valid⟩

def s1CachedNode163 : CachedPolynomialExpr 9 := .rational (0/1 : ℚ) ⟨0,0⟩

theorem s1CachedNode163_valid : s1CachedNode163.Valid := by decide +kernel

def s1CachedNode164 : CachedPolynomialExpr 9 := .add s1CachedNode162 s1CachedNode163

theorem s1CachedNode164_valid : s1CachedNode164.Valid := ⟨s1CachedNode162_valid,s1CachedNode163_valid⟩

def s1CachedNode165 : CachedPolynomialExpr 9 := .add s1CachedNode154 s1CachedNode164

theorem s1CachedNode165_valid : s1CachedNode165.Valid := ⟨s1CachedNode154_valid,s1CachedNode164_valid⟩

def s1CachedNode166 : CachedPolynomialExpr 9 := .add s1CachedNode143 s1CachedNode165

theorem s1CachedNode166_valid : s1CachedNode166.Valid := ⟨s1CachedNode143_valid,s1CachedNode165_valid⟩

def s1CachedNode167 : CachedPolynomialExpr 9 := .add s1CachedNode135 s1CachedNode166

theorem s1CachedNode167_valid : s1CachedNode167.Valid := ⟨s1CachedNode135_valid,s1CachedNode166_valid⟩

def s1CachedNode168 : CachedPolynomialExpr 9 := .add s1CachedNode104 s1CachedNode167

theorem s1CachedNode168_valid : s1CachedNode168.Valid := ⟨s1CachedNode104_valid,s1CachedNode167_valid⟩

def s1CachedNode169 : CachedPolynomialExpr 9 := .add s1CachedNode96 s1CachedNode168

theorem s1CachedNode169_valid : s1CachedNode169.Valid := ⟨s1CachedNode96_valid,s1CachedNode168_valid⟩

def s1CachedNode170 : CachedPolynomialExpr 9 := .add s1CachedNode85 s1CachedNode169

theorem s1CachedNode170_valid : s1CachedNode170.Valid := ⟨s1CachedNode85_valid,s1CachedNode169_valid⟩

def s1CachedNode171 : CachedPolynomialExpr 9 := .add s1CachedNode71 s1CachedNode170

theorem s1CachedNode171_valid : s1CachedNode171.Valid := ⟨s1CachedNode71_valid,s1CachedNode170_valid⟩

def s1CachedNode172 : CachedPolynomialExpr 9 := .add s1CachedNode63 s1CachedNode171

theorem s1CachedNode172_valid : s1CachedNode172.Valid := ⟨s1CachedNode63_valid,s1CachedNode171_valid⟩

def s1CachedNode173 : CachedPolynomialExpr 9 := .add s1CachedNode45 s1CachedNode172

theorem s1CachedNode173_valid : s1CachedNode173.Valid := ⟨s1CachedNode45_valid,s1CachedNode172_valid⟩

def s1CachedNode174 : CachedPolynomialExpr 9 := .add s1CachedNode18 s1CachedNode173

theorem s1CachedNode174_valid : s1CachedNode174.Valid := ⟨s1CachedNode18_valid,s1CachedNode173_valid⟩

def s1CachedNode175 : CachedPolynomialExpr 9 := .add s1CachedNode11 s1CachedNode174

theorem s1CachedNode175_valid : s1CachedNode175.Valid := ⟨s1CachedNode11_valid,s1CachedNode174_valid⟩

def s1CachedNode176 : CachedPolynomialExpr 9 := .neg s1CachedNode175

theorem s1CachedNode176_valid : s1CachedNode176.Valid := s1CachedNode175_valid

def s1CachedNode177 : CachedPolynomialExpr 9 := .rational (1080863910568919/1125899906842624 : ℚ) ⟨1106804644422573056,1106804644422573056⟩

theorem s1CachedNode177_valid : s1CachedNode177.Valid := by decide +kernel

def s1CachedNode178 : CachedPolynomialExpr 9 := .var 7

theorem s1CachedNode178_valid : s1CachedNode178.Valid := True.intro

def s1CachedNode179 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode26

theorem s1CachedNode179_valid : s1CachedNode179.Valid := ⟨s1CachedNode178_valid,s1CachedNode26_valid⟩

def s1CachedNode180 : CachedPolynomialExpr 9 := .add s1CachedNode1 s1CachedNode179

theorem s1CachedNode180_valid : s1CachedNode180.Valid := ⟨s1CachedNode1_valid,s1CachedNode179_valid⟩

def s1CachedNode181 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode180

theorem s1CachedNode181_valid : s1CachedNode181.Valid := ⟨s1CachedNode25_valid,s1CachedNode180_valid⟩

def s1CachedNode182 : CachedPolynomialExpr 9 := .mul s1CachedNode181 s1CachedNode180

theorem s1CachedNode182_valid : s1CachedNode182.Valid := ⟨s1CachedNode181_valid,s1CachedNode180_valid⟩

def s1CachedNode183 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode32

theorem s1CachedNode183_valid : s1CachedNode183.Valid := ⟨s1CachedNode178_valid,s1CachedNode32_valid⟩

def s1CachedNode184 : CachedPolynomialExpr 9 := .add s1CachedNode2 s1CachedNode183

theorem s1CachedNode184_valid : s1CachedNode184.Valid := ⟨s1CachedNode2_valid,s1CachedNode183_valid⟩

def s1CachedNode185 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode184

theorem s1CachedNode185_valid : s1CachedNode185.Valid := ⟨s1CachedNode25_valid,s1CachedNode184_valid⟩

def s1CachedNode186 : CachedPolynomialExpr 9 := .mul s1CachedNode185 s1CachedNode184

theorem s1CachedNode186_valid : s1CachedNode186.Valid := ⟨s1CachedNode185_valid,s1CachedNode184_valid⟩

def s1CachedNode187 : CachedPolynomialExpr 9 := .add s1CachedNode182 s1CachedNode186

theorem s1CachedNode187_valid : s1CachedNode187.Valid := ⟨s1CachedNode182_valid,s1CachedNode186_valid⟩

def s1CachedNode188 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode39

theorem s1CachedNode188_valid : s1CachedNode188.Valid := ⟨s1CachedNode178_valid,s1CachedNode39_valid⟩

def s1CachedNode189 : CachedPolynomialExpr 9 := .add s1CachedNode4 s1CachedNode188

theorem s1CachedNode189_valid : s1CachedNode189.Valid := ⟨s1CachedNode4_valid,s1CachedNode188_valid⟩

def s1CachedNode190 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode189

theorem s1CachedNode190_valid : s1CachedNode190.Valid := ⟨s1CachedNode25_valid,s1CachedNode189_valid⟩

def s1CachedNode191 : CachedPolynomialExpr 9 := .mul s1CachedNode190 s1CachedNode189

theorem s1CachedNode191_valid : s1CachedNode191.Valid := ⟨s1CachedNode190_valid,s1CachedNode189_valid⟩

def s1CachedNode192 : CachedPolynomialExpr 9 := .add s1CachedNode187 s1CachedNode191

theorem s1CachedNode192_valid : s1CachedNode192.Valid := ⟨s1CachedNode187_valid,s1CachedNode191_valid⟩

def s1CachedNode193 : CachedPolynomialExpr 9 := .mul s1CachedNode192 s1CachedNode6

theorem s1CachedNode193_valid : s1CachedNode193.Valid := ⟨s1CachedNode192_valid,s1CachedNode6_valid⟩

def s1CachedNode194 : CachedPolynomialExpr 9 := .mul s1CachedNode180 s1CachedNode184

theorem s1CachedNode194_valid : s1CachedNode194.Valid := ⟨s1CachedNode180_valid,s1CachedNode184_valid⟩

def s1CachedNode195 : CachedPolynomialExpr 9 := .mul s1CachedNode184 s1CachedNode189

theorem s1CachedNode195_valid : s1CachedNode195.Valid := ⟨s1CachedNode184_valid,s1CachedNode189_valid⟩

def s1CachedNode196 : CachedPolynomialExpr 9 := .add s1CachedNode194 s1CachedNode195

theorem s1CachedNode196_valid : s1CachedNode196.Valid := ⟨s1CachedNode194_valid,s1CachedNode195_valid⟩

def s1CachedNode197 : CachedPolynomialExpr 9 := .mul s1CachedNode189 s1CachedNode180

theorem s1CachedNode197_valid : s1CachedNode197.Valid := ⟨s1CachedNode189_valid,s1CachedNode180_valid⟩

def s1CachedNode198 : CachedPolynomialExpr 9 := .add s1CachedNode196 s1CachedNode197

theorem s1CachedNode198_valid : s1CachedNode198.Valid := ⟨s1CachedNode196_valid,s1CachedNode197_valid⟩

def s1CachedNode199 : CachedPolynomialExpr 9 := .mul s1CachedNode198 s1CachedNode6

theorem s1CachedNode199_valid : s1CachedNode199.Valid := ⟨s1CachedNode198_valid,s1CachedNode6_valid⟩

def s1CachedNode200 : CachedPolynomialExpr 9 := .mul s1CachedNode106 s1CachedNode199

theorem s1CachedNode200_valid : s1CachedNode200.Valid := ⟨s1CachedNode106_valid,s1CachedNode199_valid⟩

def s1CachedNode201 : CachedPolynomialExpr 9 := .neg s1CachedNode200

theorem s1CachedNode201_valid : s1CachedNode201.Valid := s1CachedNode200_valid

def s1CachedNode202 : CachedPolynomialExpr 9 := .add s1CachedNode193 s1CachedNode201

theorem s1CachedNode202_valid : s1CachedNode202.Valid := ⟨s1CachedNode193_valid,s1CachedNode201_valid⟩

def s1CachedNode203 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode42

theorem s1CachedNode203_valid : s1CachedNode203.Valid := ⟨s1CachedNode178_valid,s1CachedNode42_valid⟩

def s1CachedNode204 : CachedPolynomialExpr 9 := .add s1CachedNode8 s1CachedNode203

theorem s1CachedNode204_valid : s1CachedNode204.Valid := ⟨s1CachedNode8_valid,s1CachedNode203_valid⟩

def s1CachedNode205 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode204

theorem s1CachedNode205_valid : s1CachedNode205.Valid := ⟨s1CachedNode25_valid,s1CachedNode204_valid⟩

def s1CachedNode206 : CachedPolynomialExpr 9 := .mul s1CachedNode205 s1CachedNode204

theorem s1CachedNode206_valid : s1CachedNode206.Valid := ⟨s1CachedNode205_valid,s1CachedNode204_valid⟩

def s1CachedNode207 : CachedPolynomialExpr 9 := .add s1CachedNode202 s1CachedNode206

theorem s1CachedNode207_valid : s1CachedNode207.Valid := ⟨s1CachedNode202_valid,s1CachedNode206_valid⟩

def s1CachedNode208 : CachedPolynomialExpr 9 := .mul s1CachedNode177 s1CachedNode207

theorem s1CachedNode208_valid : s1CachedNode208.Valid := ⟨s1CachedNode177_valid,s1CachedNode207_valid⟩

def s1CachedNode209 : CachedPolynomialExpr 9 := .neg s1CachedNode208

theorem s1CachedNode209_valid : s1CachedNode209.Valid := s1CachedNode208_valid

def s1CachedNode210 : CachedPolynomialExpr 9 := .add s1CachedNode176 s1CachedNode209

theorem s1CachedNode210_valid : s1CachedNode210.Valid := ⟨s1CachedNode176_valid,s1CachedNode209_valid⟩

def s1CachedValue : CachedPolynomialExpr 9 := s1CachedNode210

theorem s1CachedValue_valid : s1CachedValue.Valid := s1CachedNode210_valid

theorem s1CachedValue_erase : s1CachedValue.erase = s1CertificateExpr := by decide +kernel

def s1CachedNode211 : CachedPolynomialExpr 9 := .rational (-7541973450629039/110680464442257309696 : ℚ) ⟨-78562223444053,-78562223444052⟩

theorem s1CachedNode211_valid : s1CachedNode211.Valid := by decide +kernel

def s1CachedNode212 : CachedPolynomialExpr 9 := .rational (569880289982206311878157096625703/973555660975280180349468061728768 : ℚ) ⟨674873833832860147,674873833832860148⟩

theorem s1CachedNode212_valid : s1CachedNode212.Valid := by decide +kernel

def s1CachedNode213 : CachedPolynomialExpr 9 := .rational (-182748035989146298655261272758893/243388915243820045087367015432192 : ℚ) ⟨-865668596310088384,-865668596310088383⟩

theorem s1CachedNode213_valid : s1CachedNode213.Valid := by decide +kernel

def s1CachedNode214 : CachedPolynomialExpr 9 := .rational (8774057038934945/216172782113783808 : ℚ) ⟨46794970874319706,46794970874319707⟩

theorem s1CachedNode214_valid : s1CachedNode214.Valid := by decide +kernel

def s1CachedNode215 : CachedPolynomialExpr 9 := .mul s1CachedNode214 s1CachedNode20

theorem s1CachedNode215_valid : s1CachedNode215.Valid := ⟨s1CachedNode214_valid,s1CachedNode20_valid⟩

def s1CachedNode216 : CachedPolynomialExpr 9 := .add s1CachedNode213 s1CachedNode215

theorem s1CachedNode216_valid : s1CachedNode216.Valid := ⟨s1CachedNode213_valid,s1CachedNode215_valid⟩

def s1CachedNode217 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode216

theorem s1CachedNode217_valid : s1CachedNode217.Valid := ⟨s1CachedNode20_valid,s1CachedNode216_valid⟩

def s1CachedNode218 : CachedPolynomialExpr 9 := .add s1CachedNode212 s1CachedNode217

theorem s1CachedNode218_valid : s1CachedNode218.Valid := ⟨s1CachedNode212_valid,s1CachedNode217_valid⟩

def s1CachedNode219 : CachedPolynomialExpr 9 := .rational (1060411694215663/1125899906842624 : ℚ) ⟨1085861574876838912,1085861574876838912⟩

theorem s1CachedNode219_valid : s1CachedNode219.Valid := by decide +kernel

def s1CachedNode220 : CachedPolynomialExpr 9 := .rational (-1019507261509151/1688849860263936 : ℚ) ⟨-695983623856913750,-695983623856913749⟩

theorem s1CachedNode220_valid : s1CachedNode220.Valid := by decide +kernel

def s1CachedNode221 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode20

theorem s1CachedNode221_valid : s1CachedNode221.Valid := ⟨s1CachedNode220_valid,s1CachedNode20_valid⟩

def s1CachedNode222 : CachedPolynomialExpr 9 := .add s1CachedNode219 s1CachedNode221

theorem s1CachedNode222_valid : s1CachedNode222.Valid := ⟨s1CachedNode219_valid,s1CachedNode221_valid⟩

def s1CachedNode223 : CachedPolynomialExpr 9 := .rational (321758981194718345526705266048669/973555660975280180349468061728768 : ℚ) ⟨381039177922463003,381039177922463004⟩

theorem s1CachedNode223_valid : s1CachedNode223.Valid := by decide +kernel

def s1CachedNode224 : CachedPolynomialExpr 9 := .rational (7199522257880297/9007199254740992 : ℚ) ⟨921538849008678016,921538849008678016⟩

theorem s1CachedNode224_valid : s1CachedNode224.Valid := by decide +kernel

def s1CachedNode225 : CachedPolynomialExpr 9 := .mul s1CachedNode224 s1CachedNode20

theorem s1CachedNode225_valid : s1CachedNode225.Valid := ⟨s1CachedNode224_valid,s1CachedNode20_valid⟩

def s1CachedNode226 : CachedPolynomialExpr 9 := .add s1CachedNode223 s1CachedNode225

theorem s1CachedNode226_valid : s1CachedNode226.Valid := ⟨s1CachedNode223_valid,s1CachedNode225_valid⟩

def s1CachedNode227 : CachedPolynomialExpr 9 := .rational (-187820197371309106883475032631535/121694457621910022543683507716096 : ℚ) ⟨-1779390358282826004,-1779390358282826003⟩

theorem s1CachedNode227_valid : s1CachedNode227.Valid := by decide +kernel

def s1CachedNode228 : CachedPolynomialExpr 9 := .rational (6881924343606227/3377699720527872 : ℚ) ⟨2349030175950925482,2349030175950925483⟩

theorem s1CachedNode228_valid : s1CachedNode228.Valid := by decide +kernel

def s1CachedNode229 : CachedPolynomialExpr 9 := .rational (6881924343606227/6755399441055744 : ℚ) ⟨1174515087975462741,1174515087975462742⟩

theorem s1CachedNode229_valid : s1CachedNode229.Valid := by decide +kernel

def s1CachedNode230 : CachedPolynomialExpr 9 := .mul s1CachedNode229 s1CachedNode27

theorem s1CachedNode230_valid : s1CachedNode230.Valid := ⟨s1CachedNode229_valid,s1CachedNode27_valid⟩

def s1CachedNode231 : CachedPolynomialExpr 9 := .add s1CachedNode228 s1CachedNode230

theorem s1CachedNode231_valid : s1CachedNode231.Valid := ⟨s1CachedNode228_valid,s1CachedNode230_valid⟩

def s1CachedNode232 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode231

theorem s1CachedNode232_valid : s1CachedNode232.Valid := ⟨s1CachedNode2_valid,s1CachedNode231_valid⟩

def s1CachedNode233 : CachedPolynomialExpr 9 := .add s1CachedNode227 s1CachedNode232

theorem s1CachedNode233_valid : s1CachedNode233.Valid := ⟨s1CachedNode227_valid,s1CachedNode232_valid⟩

def s1CachedNode234 : CachedPolynomialExpr 9 := .mul s1CachedNode229 s1CachedNode34

theorem s1CachedNode234_valid : s1CachedNode234.Valid := ⟨s1CachedNode229_valid,s1CachedNode34_valid⟩

def s1CachedNode235 : CachedPolynomialExpr 9 := .add s1CachedNode228 s1CachedNode234

theorem s1CachedNode235_valid : s1CachedNode235.Valid := ⟨s1CachedNode228_valid,s1CachedNode234_valid⟩

def s1CachedNode236 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode235

theorem s1CachedNode236_valid : s1CachedNode236.Valid := ⟨s1CachedNode4_valid,s1CachedNode235_valid⟩

def s1CachedNode237 : CachedPolynomialExpr 9 := .add s1CachedNode233 s1CachedNode236

theorem s1CachedNode237_valid : s1CachedNode237.Valid := ⟨s1CachedNode233_valid,s1CachedNode236_valid⟩

def s1CachedNode238 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode237

theorem s1CachedNode238_valid : s1CachedNode238.Valid := ⟨s1CachedNode1_valid,s1CachedNode237_valid⟩

def s1CachedNode239 : CachedPolynomialExpr 9 := .add s1CachedNode226 s1CachedNode238

theorem s1CachedNode239_valid : s1CachedNode239.Valid := ⟨s1CachedNode226_valid,s1CachedNode238_valid⟩

def s1CachedNode240 : CachedPolynomialExpr 9 := .rational (-7097966112403971/9007199254740992 : ℚ) ⟨-908539662387708288,-908539662387708288⟩

theorem s1CachedNode240_valid : s1CachedNode240.Valid := by decide +kernel

def s1CachedNode241 : CachedPolynomialExpr 9 := .rational (-7097966112403971/18014398509481984 : ℚ) ⟨-454269831193854144,-454269831193854144⟩

theorem s1CachedNode241_valid : s1CachedNode241.Valid := by decide +kernel

def s1CachedNode242 : CachedPolynomialExpr 9 := .mul s1CachedNode241 s1CachedNode27

theorem s1CachedNode242_valid : s1CachedNode242.Valid := ⟨s1CachedNode241_valid,s1CachedNode27_valid⟩

def s1CachedNode243 : CachedPolynomialExpr 9 := .add s1CachedNode240 s1CachedNode242

theorem s1CachedNode243_valid : s1CachedNode243.Valid := ⟨s1CachedNode240_valid,s1CachedNode242_valid⟩

def s1CachedNode244 : CachedPolynomialExpr 9 := .mul s1CachedNode86 s1CachedNode4

theorem s1CachedNode244_valid : s1CachedNode244.Valid := ⟨s1CachedNode86_valid,s1CachedNode4_valid⟩

def s1CachedNode245 : CachedPolynomialExpr 9 := .mul s1CachedNode244 s1CachedNode47

theorem s1CachedNode245_valid : s1CachedNode245.Valid := ⟨s1CachedNode244_valid,s1CachedNode47_valid⟩

def s1CachedNode246 : CachedPolynomialExpr 9 := .add s1CachedNode243 s1CachedNode245

theorem s1CachedNode246_valid : s1CachedNode246.Valid := ⟨s1CachedNode243_valid,s1CachedNode245_valid⟩

def s1CachedNode247 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode246

theorem s1CachedNode247_valid : s1CachedNode247.Valid := ⟨s1CachedNode2_valid,s1CachedNode246_valid⟩

def s1CachedNode248 : CachedPolynomialExpr 9 := .add s1CachedNode239 s1CachedNode247

theorem s1CachedNode248_valid : s1CachedNode248.Valid := ⟨s1CachedNode239_valid,s1CachedNode247_valid⟩

def s1CachedNode249 : CachedPolynomialExpr 9 := .mul s1CachedNode241 s1CachedNode34

theorem s1CachedNode249_valid : s1CachedNode249.Valid := ⟨s1CachedNode241_valid,s1CachedNode34_valid⟩

def s1CachedNode250 : CachedPolynomialExpr 9 := .add s1CachedNode240 s1CachedNode249

theorem s1CachedNode250_valid : s1CachedNode250.Valid := ⟨s1CachedNode240_valid,s1CachedNode249_valid⟩

def s1CachedNode251 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode250

theorem s1CachedNode251_valid : s1CachedNode251.Valid := ⟨s1CachedNode4_valid,s1CachedNode250_valid⟩

def s1CachedNode252 : CachedPolynomialExpr 9 := .add s1CachedNode248 s1CachedNode251

theorem s1CachedNode252_valid : s1CachedNode252.Valid := ⟨s1CachedNode248_valid,s1CachedNode251_valid⟩

def s1CachedNode253 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode252

theorem s1CachedNode253_valid : s1CachedNode253.Valid := ⟨s1CachedNode1_valid,s1CachedNode252_valid⟩

def s1CachedNode254 : CachedPolynomialExpr 9 := .add s1CachedNode222 s1CachedNode253

theorem s1CachedNode254_valid : s1CachedNode254.Valid := ⟨s1CachedNode222_valid,s1CachedNode253_valid⟩

def s1CachedNode255 : CachedPolynomialExpr 9 := .rational (-1080863910568919/1688849860263936 : ℚ) ⟨-737869762948382038,-737869762948382037⟩

theorem s1CachedNode255_valid : s1CachedNode255.Valid := by decide +kernel

def s1CachedNode256 : CachedPolynomialExpr 9 := .rational (-1080863910568919/844424930131968 : ℚ) ⟨-1475739525896764075,-1475739525896764074⟩

theorem s1CachedNode256_valid : s1CachedNode256.Valid := by decide +kernel

def s1CachedNode257 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode20

theorem s1CachedNode257_valid : s1CachedNode257.Valid := ⟨s1CachedNode256_valid,s1CachedNode20_valid⟩

def s1CachedNode258 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode257

theorem s1CachedNode258_valid : s1CachedNode258.Valid := ⟨s1CachedNode255_valid,s1CachedNode257_valid⟩

def s1CachedNode259 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode178

theorem s1CachedNode259_valid : s1CachedNode259.Valid := ⟨s1CachedNode20_valid,s1CachedNode178_valid⟩

def s1CachedNode260 : CachedPolynomialExpr 9 := .rational (1080863910568919/1688849860263936 : ℚ) ⟨737869762948382037,737869762948382038⟩

theorem s1CachedNode260_valid : s1CachedNode260.Valid := by decide +kernel

def s1CachedNode261 : CachedPolynomialExpr 9 := .mul s1CachedNode260 s1CachedNode20

theorem s1CachedNode261_valid : s1CachedNode261.Valid := ⟨s1CachedNode260_valid,s1CachedNode20_valid⟩

def s1CachedNode262 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode261

theorem s1CachedNode262_valid : s1CachedNode262.Valid := ⟨s1CachedNode260_valid,s1CachedNode261_valid⟩

def s1CachedNode263 : CachedPolynomialExpr 9 := .mul s1CachedNode259 s1CachedNode262

theorem s1CachedNode263_valid : s1CachedNode263.Valid := ⟨s1CachedNode259_valid,s1CachedNode262_valid⟩

def s1CachedNode264 : CachedPolynomialExpr 9 := .add s1CachedNode258 s1CachedNode263

theorem s1CachedNode264_valid : s1CachedNode264.Valid := ⟨s1CachedNode258_valid,s1CachedNode263_valid⟩

def s1CachedNode265 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode264

theorem s1CachedNode265_valid : s1CachedNode265.Valid := ⟨s1CachedNode178_valid,s1CachedNode264_valid⟩

def s1CachedNode266 : CachedPolynomialExpr 9 := .add s1CachedNode254 s1CachedNode265

theorem s1CachedNode266_valid : s1CachedNode266.Valid := ⟨s1CachedNode254_valid,s1CachedNode265_valid⟩

def s1CachedNode267 : CachedPolynomialExpr 9 := .rational (1019507261509151/1688849860263936 : ℚ) ⟨695983623856913749,695983623856913750⟩

theorem s1CachedNode267_valid : s1CachedNode267.Valid := by decide +kernel

def s1CachedNode268 : CachedPolynomialExpr 9 := .mul s1CachedNode267 s1CachedNode2

theorem s1CachedNode268_valid : s1CachedNode268.Valid := ⟨s1CachedNode267_valid,s1CachedNode2_valid⟩

def s1CachedNode269 : CachedPolynomialExpr 9 := .mul s1CachedNode268 s1CachedNode4

theorem s1CachedNode269_valid : s1CachedNode269.Valid := ⟨s1CachedNode268_valid,s1CachedNode4_valid⟩

def s1CachedNode270 : CachedPolynomialExpr 9 := .mul s1CachedNode269 s1CachedNode47

theorem s1CachedNode270_valid : s1CachedNode270.Valid := ⟨s1CachedNode269_valid,s1CachedNode47_valid⟩

def s1CachedNode271 : CachedPolynomialExpr 9 := .add s1CachedNode266 s1CachedNode270

theorem s1CachedNode271_valid : s1CachedNode271.Valid := ⟨s1CachedNode266_valid,s1CachedNode270_valid⟩

def s1CachedNode272 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode271

theorem s1CachedNode272_valid : s1CachedNode272.Valid := ⟨s1CachedNode1_valid,s1CachedNode271_valid⟩

def s1CachedNode273 : CachedPolynomialExpr 9 := .add s1CachedNode218 s1CachedNode272

theorem s1CachedNode273_valid : s1CachedNode273.Valid := ⟨s1CachedNode218_valid,s1CachedNode272_valid⟩

def s1CachedNode274 : CachedPolynomialExpr 9 := .rational (-53858449552681981/54043195528445952 : ℚ) ⟨-1148980257123882262,-1148980257123882261⟩

theorem s1CachedNode274_valid : s1CachedNode274.Valid := by decide +kernel

def s1CachedNode275 : CachedPolynomialExpr 9 := .mul s1CachedNode211 s1CachedNode47

theorem s1CachedNode275_valid : s1CachedNode275.Valid := ⟨s1CachedNode211_valid,s1CachedNode47_valid⟩

def s1CachedNode276 : CachedPolynomialExpr 9 := .add s1CachedNode274 s1CachedNode275

theorem s1CachedNode276_valid : s1CachedNode276.Valid := ⟨s1CachedNode274_valid,s1CachedNode275_valid⟩

def s1CachedNode277 : CachedPolynomialExpr 9 := .rational (2521529215217977/54043195528445952 : ℚ) ⟨53792623257983509,53792623257983510⟩

theorem s1CachedNode277_valid : s1CachedNode277.Valid := by decide +kernel

def s1CachedNode278 : CachedPolynomialExpr 9 := .mul s1CachedNode277 s1CachedNode27

theorem s1CachedNode278_valid : s1CachedNode278.Valid := ⟨s1CachedNode277_valid,s1CachedNode27_valid⟩

def s1CachedNode279 : CachedPolynomialExpr 9 := .add s1CachedNode276 s1CachedNode278

theorem s1CachedNode279_valid : s1CachedNode279.Valid := ⟨s1CachedNode276_valid,s1CachedNode278_valid⟩

def s1CachedNode280 : CachedPolynomialExpr 9 := .rational (29356921275348481/54043195528445952 : ℚ) ⟨626280987207434261,626280987207434262⟩

theorem s1CachedNode280_valid : s1CachedNode280.Valid := by decide +kernel

def s1CachedNode281 : CachedPolynomialExpr 9 := .rational (1118141335838771/2251799813685248 : ℚ) ⟨572488363949450752,572488363949450752⟩

theorem s1CachedNode281_valid : s1CachedNode281.Valid := by decide +kernel

def s1CachedNode282 : CachedPolynomialExpr 9 := .mul s1CachedNode281 s1CachedNode27

theorem s1CachedNode282_valid : s1CachedNode282.Valid := ⟨s1CachedNode281_valid,s1CachedNode27_valid⟩

def s1CachedNode283 : CachedPolynomialExpr 9 := .add s1CachedNode280 s1CachedNode282

theorem s1CachedNode283_valid : s1CachedNode283.Valid := ⟨s1CachedNode280_valid,s1CachedNode282_valid⟩

def s1CachedNode284 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode283

theorem s1CachedNode284_valid : s1CachedNode284.Valid := ⟨s1CachedNode20_valid,s1CachedNode283_valid⟩

def s1CachedNode285 : CachedPolynomialExpr 9 := .add s1CachedNode279 s1CachedNode284

theorem s1CachedNode285_valid : s1CachedNode285.Valid := ⟨s1CachedNode279_valid,s1CachedNode284_valid⟩

def s1CachedNode286 : CachedPolynomialExpr 9 := .rational (-2365988704134657/18014398509481984 : ℚ) ⟨-151423277064618048,-151423277064618048⟩

theorem s1CachedNode286_valid : s1CachedNode286.Valid := by decide +kernel

def s1CachedNode287 : CachedPolynomialExpr 9 := .mul s1CachedNode286 s1CachedNode20

theorem s1CachedNode287_valid : s1CachedNode287.Valid := ⟨s1CachedNode286_valid,s1CachedNode20_valid⟩

def s1CachedNode288 : CachedPolynomialExpr 9 := .add s1CachedNode286 s1CachedNode287

theorem s1CachedNode288_valid : s1CachedNode288.Valid := ⟨s1CachedNode286_valid,s1CachedNode287_valid⟩

def s1CachedNode289 : CachedPolynomialExpr 9 := .rational (6881924343606227/27021597764222976 : ℚ) ⟨293628771993865685,293628771993865686⟩

theorem s1CachedNode289_valid : s1CachedNode289.Valid := by decide +kernel

def s1CachedNode290 : CachedPolynomialExpr 9 := .mul s1CachedNode289 s1CachedNode20

theorem s1CachedNode290_valid : s1CachedNode290.Valid := ⟨s1CachedNode289_valid,s1CachedNode20_valid⟩

def s1CachedNode291 : CachedPolynomialExpr 9 := .add s1CachedNode289 s1CachedNode290

theorem s1CachedNode291_valid : s1CachedNode291.Valid := ⟨s1CachedNode289_valid,s1CachedNode290_valid⟩

def s1CachedNode292 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode291

theorem s1CachedNode292_valid : s1CachedNode292.Valid := ⟨s1CachedNode2_valid,s1CachedNode291_valid⟩

def s1CachedNode293 : CachedPolynomialExpr 9 := .add s1CachedNode288 s1CachedNode292

theorem s1CachedNode293_valid : s1CachedNode293.Valid := ⟨s1CachedNode288_valid,s1CachedNode292_valid⟩

def s1CachedNode294 : CachedPolynomialExpr 9 := .rational (-7199522257880297/27021597764222976 : ℚ) ⟨-307179616336226006,-307179616336226005⟩

theorem s1CachedNode294_valid : s1CachedNode294.Valid := by decide +kernel

def s1CachedNode295 : CachedPolynomialExpr 9 := .mul s1CachedNode294 s1CachedNode4

theorem s1CachedNode295_valid : s1CachedNode295.Valid := ⟨s1CachedNode294_valid,s1CachedNode4_valid⟩

def s1CachedNode296 : CachedPolynomialExpr 9 := .mul s1CachedNode295 s1CachedNode47

theorem s1CachedNode296_valid : s1CachedNode296.Valid := ⟨s1CachedNode295_valid,s1CachedNode47_valid⟩

def s1CachedNode297 : CachedPolynomialExpr 9 := .add s1CachedNode293 s1CachedNode296

theorem s1CachedNode297_valid : s1CachedNode297.Valid := ⟨s1CachedNode293_valid,s1CachedNode296_valid⟩

def s1CachedNode298 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode297

theorem s1CachedNode298_valid : s1CachedNode298.Valid := ⟨s1CachedNode2_valid,s1CachedNode297_valid⟩

def s1CachedNode299 : CachedPolynomialExpr 9 := .rational (1019507261509151/3377699720527872 : ℚ) ⟨347991811928456874,347991811928456875⟩

theorem s1CachedNode299_valid : s1CachedNode299.Valid := by decide +kernel

def s1CachedNode300 : CachedPolynomialExpr 9 := .mul s1CachedNode299 s1CachedNode4

theorem s1CachedNode300_valid : s1CachedNode300.Valid := ⟨s1CachedNode299_valid,s1CachedNode4_valid⟩

def s1CachedNode301 : CachedPolynomialExpr 9 := .mul s1CachedNode300 s1CachedNode47

theorem s1CachedNode301_valid : s1CachedNode301.Valid := ⟨s1CachedNode300_valid,s1CachedNode47_valid⟩

def s1CachedNode302 : CachedPolynomialExpr 9 := .add s1CachedNode298 s1CachedNode301

theorem s1CachedNode302_valid : s1CachedNode302.Valid := ⟨s1CachedNode298_valid,s1CachedNode301_valid⟩

def s1CachedNode303 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode302

theorem s1CachedNode303_valid : s1CachedNode303.Valid := ⟨s1CachedNode2_valid,s1CachedNode302_valid⟩

def s1CachedNode304 : CachedPolynomialExpr 9 := .add s1CachedNode285 s1CachedNode303

theorem s1CachedNode304_valid : s1CachedNode304.Valid := ⟨s1CachedNode285_valid,s1CachedNode303_valid⟩

def s1CachedNode305 : CachedPolynomialExpr 9 := .mul s1CachedNode299 s1CachedNode47

theorem s1CachedNode305_valid : s1CachedNode305.Valid := ⟨s1CachedNode299_valid,s1CachedNode47_valid⟩

def s1CachedNode306 : CachedPolynomialExpr 9 := .add s1CachedNode305 s1CachedNode296

theorem s1CachedNode306_valid : s1CachedNode306.Valid := ⟨s1CachedNode305_valid,s1CachedNode296_valid⟩

def s1CachedNode307 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode306

theorem s1CachedNode307_valid : s1CachedNode307.Valid := ⟨s1CachedNode4_valid,s1CachedNode306_valid⟩

def s1CachedNode308 : CachedPolynomialExpr 9 := .add s1CachedNode12 s1CachedNode307

theorem s1CachedNode308_valid : s1CachedNode308.Valid := ⟨s1CachedNode12_valid,s1CachedNode307_valid⟩

def s1CachedNode309 : CachedPolynomialExpr 9 := .rational (-4259548906037743/54043195528445952 : ℚ) ⟨-90870376662138518,-90870376662138517⟩

theorem s1CachedNode309_valid : s1CachedNode309.Valid := by decide +kernel

def s1CachedNode310 : CachedPolynomialExpr 9 := .rational (-8774057038934945/216172782113783808 : ℚ) ⟨-46794970874319707,-46794970874319706⟩

theorem s1CachedNode310_valid : s1CachedNode310.Valid := by decide +kernel

def s1CachedNode311 : CachedPolynomialExpr 9 := .mul s1CachedNode310 s1CachedNode20

theorem s1CachedNode311_valid : s1CachedNode311.Valid := ⟨s1CachedNode310_valid,s1CachedNode20_valid⟩

def s1CachedNode312 : CachedPolynomialExpr 9 := .add s1CachedNode309 s1CachedNode311

theorem s1CachedNode312_valid : s1CachedNode312.Valid := ⟨s1CachedNode309_valid,s1CachedNode311_valid⟩

def s1CachedNode313 : CachedPolynomialExpr 9 := .mul s1CachedNode310 s1CachedNode27

theorem s1CachedNode313_valid : s1CachedNode313.Valid := ⟨s1CachedNode310_valid,s1CachedNode27_valid⟩

def s1CachedNode314 : CachedPolynomialExpr 9 := .add s1CachedNode312 s1CachedNode313

theorem s1CachedNode314_valid : s1CachedNode314.Valid := ⟨s1CachedNode312_valid,s1CachedNode313_valid⟩

def s1CachedNode315 : CachedPolynomialExpr 9 := .mul s1CachedNode310 s1CachedNode34

theorem s1CachedNode315_valid : s1CachedNode315.Valid := ⟨s1CachedNode310_valid,s1CachedNode34_valid⟩

def s1CachedNode316 : CachedPolynomialExpr 9 := .add s1CachedNode314 s1CachedNode315

theorem s1CachedNode316_valid : s1CachedNode316.Valid := ⟨s1CachedNode314_valid,s1CachedNode315_valid⟩

def s1CachedNode317 : CachedPolynomialExpr 9 := .mul s1CachedNode47 s1CachedNode316

theorem s1CachedNode317_valid : s1CachedNode317.Valid := ⟨s1CachedNode47_valid,s1CachedNode316_valid⟩

def s1CachedNode318 : CachedPolynomialExpr 9 := .add s1CachedNode308 s1CachedNode317

theorem s1CachedNode318_valid : s1CachedNode318.Valid := ⟨s1CachedNode308_valid,s1CachedNode317_valid⟩

def s1CachedNode319 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode318

theorem s1CachedNode319_valid : s1CachedNode319.Valid := ⟨s1CachedNode4_valid,s1CachedNode318_valid⟩

def s1CachedNode320 : CachedPolynomialExpr 9 := .add s1CachedNode304 s1CachedNode319

theorem s1CachedNode320_valid : s1CachedNode320.Valid := ⟨s1CachedNode304_valid,s1CachedNode319_valid⟩

def s1CachedNode321 : CachedPolynomialExpr 9 := .mul s1CachedNode260 s1CachedNode27

theorem s1CachedNode321_valid : s1CachedNode321.Valid := ⟨s1CachedNode260_valid,s1CachedNode27_valid⟩

def s1CachedNode322 : CachedPolynomialExpr 9 := .add s1CachedNode262 s1CachedNode321

theorem s1CachedNode322_valid : s1CachedNode322.Valid := ⟨s1CachedNode262_valid,s1CachedNode321_valid⟩

def s1CachedNode323 : CachedPolynomialExpr 9 := .mul s1CachedNode255 s1CachedNode27

theorem s1CachedNode323_valid : s1CachedNode323.Valid := ⟨s1CachedNode255_valid,s1CachedNode27_valid⟩

def s1CachedNode324 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode323

theorem s1CachedNode324_valid : s1CachedNode324.Valid := ⟨s1CachedNode255_valid,s1CachedNode323_valid⟩

def s1CachedNode325 : CachedPolynomialExpr 9 := .mul s1CachedNode259 s1CachedNode324

theorem s1CachedNode325_valid : s1CachedNode325.Valid := ⟨s1CachedNode259_valid,s1CachedNode324_valid⟩

def s1CachedNode326 : CachedPolynomialExpr 9 := .add s1CachedNode322 s1CachedNode325

theorem s1CachedNode326_valid : s1CachedNode326.Valid := ⟨s1CachedNode322_valid,s1CachedNode325_valid⟩

def s1CachedNode327 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode326

theorem s1CachedNode327_valid : s1CachedNode327.Valid := ⟨s1CachedNode178_valid,s1CachedNode326_valid⟩

def s1CachedNode328 : CachedPolynomialExpr 9 := .add s1CachedNode320 s1CachedNode327

theorem s1CachedNode328_valid : s1CachedNode328.Valid := ⟨s1CachedNode320_valid,s1CachedNode327_valid⟩

def s1CachedNode329 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode328

theorem s1CachedNode329_valid : s1CachedNode329.Valid := ⟨s1CachedNode2_valid,s1CachedNode328_valid⟩

def s1CachedNode330 : CachedPolynomialExpr 9 := .add s1CachedNode273 s1CachedNode329

theorem s1CachedNode330_valid : s1CachedNode330.Valid := ⟨s1CachedNode273_valid,s1CachedNode329_valid⟩

def s1CachedNode331 : CachedPolynomialExpr 9 := .mul s1CachedNode277 s1CachedNode34

theorem s1CachedNode331_valid : s1CachedNode331.Valid := ⟨s1CachedNode277_valid,s1CachedNode34_valid⟩

def s1CachedNode332 : CachedPolynomialExpr 9 := .add s1CachedNode276 s1CachedNode331

theorem s1CachedNode332_valid : s1CachedNode332.Valid := ⟨s1CachedNode276_valid,s1CachedNode331_valid⟩

def s1CachedNode333 : CachedPolynomialExpr 9 := .mul s1CachedNode281 s1CachedNode34

theorem s1CachedNode333_valid : s1CachedNode333.Valid := ⟨s1CachedNode281_valid,s1CachedNode34_valid⟩

def s1CachedNode334 : CachedPolynomialExpr 9 := .add s1CachedNode280 s1CachedNode333

theorem s1CachedNode334_valid : s1CachedNode334.Valid := ⟨s1CachedNode280_valid,s1CachedNode333_valid⟩

def s1CachedNode335 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode334

theorem s1CachedNode335_valid : s1CachedNode335.Valid := ⟨s1CachedNode20_valid,s1CachedNode334_valid⟩

def s1CachedNode336 : CachedPolynomialExpr 9 := .add s1CachedNode332 s1CachedNode335

theorem s1CachedNode336_valid : s1CachedNode336.Valid := ⟨s1CachedNode332_valid,s1CachedNode335_valid⟩

def s1CachedNode337 : CachedPolynomialExpr 9 := .mul s1CachedNode260 s1CachedNode34

theorem s1CachedNode337_valid : s1CachedNode337.Valid := ⟨s1CachedNode260_valid,s1CachedNode34_valid⟩

def s1CachedNode338 : CachedPolynomialExpr 9 := .add s1CachedNode262 s1CachedNode337

theorem s1CachedNode338_valid : s1CachedNode338.Valid := ⟨s1CachedNode262_valid,s1CachedNode337_valid⟩

def s1CachedNode339 : CachedPolynomialExpr 9 := .mul s1CachedNode255 s1CachedNode34

theorem s1CachedNode339_valid : s1CachedNode339.Valid := ⟨s1CachedNode255_valid,s1CachedNode34_valid⟩

def s1CachedNode340 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode339

theorem s1CachedNode340_valid : s1CachedNode340.Valid := ⟨s1CachedNode255_valid,s1CachedNode339_valid⟩

def s1CachedNode341 : CachedPolynomialExpr 9 := .mul s1CachedNode259 s1CachedNode340

theorem s1CachedNode341_valid : s1CachedNode341.Valid := ⟨s1CachedNode259_valid,s1CachedNode340_valid⟩

def s1CachedNode342 : CachedPolynomialExpr 9 := .add s1CachedNode338 s1CachedNode341

theorem s1CachedNode342_valid : s1CachedNode342.Valid := ⟨s1CachedNode338_valid,s1CachedNode341_valid⟩

def s1CachedNode343 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode342

theorem s1CachedNode343_valid : s1CachedNode343.Valid := ⟨s1CachedNode178_valid,s1CachedNode342_valid⟩

def s1CachedNode344 : CachedPolynomialExpr 9 := .add s1CachedNode336 s1CachedNode343

theorem s1CachedNode344_valid : s1CachedNode344.Valid := ⟨s1CachedNode336_valid,s1CachedNode343_valid⟩

def s1CachedNode345 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode291

theorem s1CachedNode345_valid : s1CachedNode345.Valid := ⟨s1CachedNode4_valid,s1CachedNode291_valid⟩

def s1CachedNode346 : CachedPolynomialExpr 9 := .add s1CachedNode288 s1CachedNode345

theorem s1CachedNode346_valid : s1CachedNode346.Valid := ⟨s1CachedNode288_valid,s1CachedNode345_valid⟩

def s1CachedNode347 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode346

theorem s1CachedNode347_valid : s1CachedNode347.Valid := ⟨s1CachedNode81_valid,s1CachedNode346_valid⟩

def s1CachedNode348 : CachedPolynomialExpr 9 := .add s1CachedNode344 s1CachedNode347

theorem s1CachedNode348_valid : s1CachedNode348.Valid := ⟨s1CachedNode344_valid,s1CachedNode347_valid⟩

def s1CachedNode349 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode348

theorem s1CachedNode349_valid : s1CachedNode349.Valid := ⟨s1CachedNode4_valid,s1CachedNode348_valid⟩

def s1CachedNode350 : CachedPolynomialExpr 9 := .add s1CachedNode330 s1CachedNode349

theorem s1CachedNode350_valid : s1CachedNode350.Valid := ⟨s1CachedNode330_valid,s1CachedNode349_valid⟩

def s1CachedNode351 : CachedPolynomialExpr 9 := .mul s1CachedNode261 s1CachedNode178

theorem s1CachedNode351_valid : s1CachedNode351.Valid := ⟨s1CachedNode261_valid,s1CachedNode178_valid⟩

def s1CachedNode352 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode351

theorem s1CachedNode352_valid : s1CachedNode352.Valid := ⟨s1CachedNode255_valid,s1CachedNode351_valid⟩

def s1CachedNode353 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode352

theorem s1CachedNode353_valid : s1CachedNode353.Valid := ⟨s1CachedNode178_valid,s1CachedNode352_valid⟩

def s1CachedNode354 : CachedPolynomialExpr 9 := .add s1CachedNode350 s1CachedNode353

theorem s1CachedNode354_valid : s1CachedNode354.Valid := ⟨s1CachedNode350_valid,s1CachedNode353_valid⟩

def s1CachedNode355 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode354

theorem s1CachedNode355_valid : s1CachedNode355.Valid := ⟨s1CachedNode1_valid,s1CachedNode354_valid⟩

def s1CachedNode356 : CachedPolynomialExpr 9 := .add s1CachedNode211 s1CachedNode355

theorem s1CachedNode356_valid : s1CachedNode356.Valid := ⟨s1CachedNode211_valid,s1CachedNode355_valid⟩

def s1CachedGradient0 : CachedPolynomialExpr 9 := s1CachedNode356

theorem s1CachedGradient0_valid : s1CachedGradient0.Valid := s1CachedNode356_valid

theorem s1CachedGradient0_erase : s1CachedGradient0.erase = s1HornerGradient0 := by decide +kernel

def s1CachedNode357 : CachedPolynomialExpr 9 := .mul s1CachedNode286 s1CachedNode27

theorem s1CachedNode357_valid : s1CachedNode357.Valid := ⟨s1CachedNode286_valid,s1CachedNode27_valid⟩

def s1CachedNode358 : CachedPolynomialExpr 9 := .add s1CachedNode286 s1CachedNode357

theorem s1CachedNode358_valid : s1CachedNode358.Valid := ⟨s1CachedNode286_valid,s1CachedNode357_valid⟩

def s1CachedNode359 : CachedPolynomialExpr 9 := .add s1CachedNode358 s1CachedNode296

theorem s1CachedNode359_valid : s1CachedNode359.Valid := ⟨s1CachedNode358_valid,s1CachedNode296_valid⟩

def s1CachedNode360 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode359

theorem s1CachedNode360_valid : s1CachedNode360.Valid := ⟨s1CachedNode2_valid,s1CachedNode359_valid⟩

def s1CachedNode361 : CachedPolynomialExpr 9 := .mul s1CachedNode289 s1CachedNode27

theorem s1CachedNode361_valid : s1CachedNode361.Valid := ⟨s1CachedNode289_valid,s1CachedNode27_valid⟩

def s1CachedNode362 : CachedPolynomialExpr 9 := .add s1CachedNode289 s1CachedNode361

theorem s1CachedNode362_valid : s1CachedNode362.Valid := ⟨s1CachedNode289_valid,s1CachedNode361_valid⟩

def s1CachedNode363 : CachedPolynomialExpr 9 := .mul s1CachedNode13 s1CachedNode362

theorem s1CachedNode363_valid : s1CachedNode363.Valid := ⟨s1CachedNode13_valid,s1CachedNode362_valid⟩

def s1CachedNode364 : CachedPolynomialExpr 9 := .add s1CachedNode360 s1CachedNode363

theorem s1CachedNode364_valid : s1CachedNode364.Valid := ⟨s1CachedNode360_valid,s1CachedNode363_valid⟩

def s1CachedNode365 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode364

theorem s1CachedNode365_valid : s1CachedNode365.Valid := ⟨s1CachedNode1_valid,s1CachedNode364_valid⟩

def s1CachedNode366 : CachedPolynomialExpr 9 := .mul s1CachedNode299 s1CachedNode2

theorem s1CachedNode366_valid : s1CachedNode366.Valid := ⟨s1CachedNode299_valid,s1CachedNode2_valid⟩

def s1CachedNode367 : CachedPolynomialExpr 9 := .mul s1CachedNode366 s1CachedNode4

theorem s1CachedNode367_valid : s1CachedNode367.Valid := ⟨s1CachedNode366_valid,s1CachedNode4_valid⟩

def s1CachedNode368 : CachedPolynomialExpr 9 := .mul s1CachedNode367 s1CachedNode47

theorem s1CachedNode368_valid : s1CachedNode368.Valid := ⟨s1CachedNode367_valid,s1CachedNode47_valid⟩

def s1CachedNode369 : CachedPolynomialExpr 9 := .add s1CachedNode365 s1CachedNode368

theorem s1CachedNode369_valid : s1CachedNode369.Valid := ⟨s1CachedNode365_valid,s1CachedNode368_valid⟩

def s1CachedNode370 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode369

theorem s1CachedNode370_valid : s1CachedNode370.Valid := ⟨s1CachedNode1_valid,s1CachedNode369_valid⟩

def s1CachedNode371 : CachedPolynomialExpr 9 := .mul s1CachedNode280 s1CachedNode27

theorem s1CachedNode371_valid : s1CachedNode371.Valid := ⟨s1CachedNode280_valid,s1CachedNode27_valid⟩

def s1CachedNode372 : CachedPolynomialExpr 9 := .add s1CachedNode276 s1CachedNode371

theorem s1CachedNode372_valid : s1CachedNode372.Valid := ⟨s1CachedNode276_valid,s1CachedNode371_valid⟩

def s1CachedNode373 : CachedPolynomialExpr 9 := .add s1CachedNode277 s1CachedNode282

theorem s1CachedNode373_valid : s1CachedNode373.Valid := ⟨s1CachedNode277_valid,s1CachedNode282_valid⟩

def s1CachedNode374 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode373

theorem s1CachedNode374_valid : s1CachedNode374.Valid := ⟨s1CachedNode20_valid,s1CachedNode373_valid⟩

def s1CachedNode375 : CachedPolynomialExpr 9 := .add s1CachedNode372 s1CachedNode374

theorem s1CachedNode375_valid : s1CachedNode375.Valid := ⟨s1CachedNode372_valid,s1CachedNode374_valid⟩

def s1CachedNode376 : CachedPolynomialExpr 9 := .mul s1CachedNode241 s1CachedNode20

theorem s1CachedNode376_valid : s1CachedNode376.Valid := ⟨s1CachedNode241_valid,s1CachedNode20_valid⟩

def s1CachedNode377 : CachedPolynomialExpr 9 := .add s1CachedNode240 s1CachedNode376

theorem s1CachedNode377_valid : s1CachedNode377.Valid := ⟨s1CachedNode240_valid,s1CachedNode376_valid⟩

def s1CachedNode378 : CachedPolynomialExpr 9 := .mul s1CachedNode229 s1CachedNode20

theorem s1CachedNode378_valid : s1CachedNode378.Valid := ⟨s1CachedNode229_valid,s1CachedNode20_valid⟩

def s1CachedNode379 : CachedPolynomialExpr 9 := .add s1CachedNode228 s1CachedNode378

theorem s1CachedNode379_valid : s1CachedNode379.Valid := ⟨s1CachedNode228_valid,s1CachedNode378_valid⟩

def s1CachedNode380 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode379

theorem s1CachedNode380_valid : s1CachedNode380.Valid := ⟨s1CachedNode2_valid,s1CachedNode379_valid⟩

def s1CachedNode381 : CachedPolynomialExpr 9 := .add s1CachedNode377 s1CachedNode380

theorem s1CachedNode381_valid : s1CachedNode381.Valid := ⟨s1CachedNode377_valid,s1CachedNode380_valid⟩

def s1CachedNode382 : CachedPolynomialExpr 9 := .add s1CachedNode381 s1CachedNode245

theorem s1CachedNode382_valid : s1CachedNode382.Valid := ⟨s1CachedNode381_valid,s1CachedNode245_valid⟩

def s1CachedNode383 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode382

theorem s1CachedNode383_valid : s1CachedNode383.Valid := ⟨s1CachedNode2_valid,s1CachedNode382_valid⟩

def s1CachedNode384 : CachedPolynomialExpr 9 := .mul s1CachedNode267 s1CachedNode4

theorem s1CachedNode384_valid : s1CachedNode384.Valid := ⟨s1CachedNode267_valid,s1CachedNode4_valid⟩

def s1CachedNode385 : CachedPolynomialExpr 9 := .mul s1CachedNode384 s1CachedNode47

theorem s1CachedNode385_valid : s1CachedNode385.Valid := ⟨s1CachedNode384_valid,s1CachedNode47_valid⟩

def s1CachedNode386 : CachedPolynomialExpr 9 := .add s1CachedNode383 s1CachedNode385

theorem s1CachedNode386_valid : s1CachedNode386.Valid := ⟨s1CachedNode383_valid,s1CachedNode385_valid⟩

def s1CachedNode387 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode386

theorem s1CachedNode387_valid : s1CachedNode387.Valid := ⟨s1CachedNode2_valid,s1CachedNode386_valid⟩

def s1CachedNode388 : CachedPolynomialExpr 9 := .add s1CachedNode375 s1CachedNode387

theorem s1CachedNode388_valid : s1CachedNode388.Valid := ⟨s1CachedNode375_valid,s1CachedNode387_valid⟩

def s1CachedNode389 : CachedPolynomialExpr 9 := .add s1CachedNode388 s1CachedNode319

theorem s1CachedNode389_valid : s1CachedNode389.Valid := ⟨s1CachedNode388_valid,s1CachedNode319_valid⟩

def s1CachedNode390 : CachedPolynomialExpr 9 := .mul s1CachedNode255 s1CachedNode20

theorem s1CachedNode390_valid : s1CachedNode390.Valid := ⟨s1CachedNode255_valid,s1CachedNode20_valid⟩

def s1CachedNode391 : CachedPolynomialExpr 9 := .mul s1CachedNode390 s1CachedNode27

theorem s1CachedNode391_valid : s1CachedNode391.Valid := ⟨s1CachedNode390_valid,s1CachedNode27_valid⟩

def s1CachedNode392 : CachedPolynomialExpr 9 := .add s1CachedNode323 s1CachedNode391

theorem s1CachedNode392_valid : s1CachedNode392.Valid := ⟨s1CachedNode323_valid,s1CachedNode391_valid⟩

def s1CachedNode393 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode392

theorem s1CachedNode393_valid : s1CachedNode393.Valid := ⟨s1CachedNode178_valid,s1CachedNode392_valid⟩

def s1CachedNode394 : CachedPolynomialExpr 9 := .add s1CachedNode322 s1CachedNode393

theorem s1CachedNode394_valid : s1CachedNode394.Valid := ⟨s1CachedNode322_valid,s1CachedNode393_valid⟩

def s1CachedNode395 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode394

theorem s1CachedNode395_valid : s1CachedNode395.Valid := ⟨s1CachedNode178_valid,s1CachedNode394_valid⟩

def s1CachedNode396 : CachedPolynomialExpr 9 := .add s1CachedNode389 s1CachedNode395

theorem s1CachedNode396_valid : s1CachedNode396.Valid := ⟨s1CachedNode389_valid,s1CachedNode395_valid⟩

def s1CachedNode397 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode396

theorem s1CachedNode397_valid : s1CachedNode397.Valid := ⟨s1CachedNode2_valid,s1CachedNode396_valid⟩

def s1CachedNode398 : CachedPolynomialExpr 9 := .add s1CachedNode370 s1CachedNode397

theorem s1CachedNode398_valid : s1CachedNode398.Valid := ⟨s1CachedNode370_valid,s1CachedNode397_valid⟩

def s1CachedNode399 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode398

theorem s1CachedNode399_valid : s1CachedNode399.Valid := ⟨s1CachedNode1_valid,s1CachedNode398_valid⟩

def s1CachedNode400 : CachedPolynomialExpr 9 := .add s1CachedNode211 s1CachedNode399

theorem s1CachedNode400_valid : s1CachedNode400.Valid := ⟨s1CachedNode211_valid,s1CachedNode399_valid⟩

def s1CachedNode401 : CachedPolynomialExpr 9 := .mul s1CachedNode214 s1CachedNode27

theorem s1CachedNode401_valid : s1CachedNode401.Valid := ⟨s1CachedNode214_valid,s1CachedNode27_valid⟩

def s1CachedNode402 : CachedPolynomialExpr 9 := .add s1CachedNode213 s1CachedNode401

theorem s1CachedNode402_valid : s1CachedNode402.Valid := ⟨s1CachedNode213_valid,s1CachedNode401_valid⟩

def s1CachedNode403 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode402

theorem s1CachedNode403_valid : s1CachedNode403.Valid := ⟨s1CachedNode27_valid,s1CachedNode402_valid⟩

def s1CachedNode404 : CachedPolynomialExpr 9 := .add s1CachedNode212 s1CachedNode403

theorem s1CachedNode404_valid : s1CachedNode404.Valid := ⟨s1CachedNode212_valid,s1CachedNode403_valid⟩

def s1CachedNode405 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode27

theorem s1CachedNode405_valid : s1CachedNode405.Valid := ⟨s1CachedNode220_valid,s1CachedNode27_valid⟩

def s1CachedNode406 : CachedPolynomialExpr 9 := .add s1CachedNode219 s1CachedNode405

theorem s1CachedNode406_valid : s1CachedNode406.Valid := ⟨s1CachedNode219_valid,s1CachedNode405_valid⟩

def s1CachedNode407 : CachedPolynomialExpr 9 := .mul s1CachedNode224 s1CachedNode27

theorem s1CachedNode407_valid : s1CachedNode407.Valid := ⟨s1CachedNode224_valid,s1CachedNode27_valid⟩

def s1CachedNode408 : CachedPolynomialExpr 9 := .add s1CachedNode223 s1CachedNode407

theorem s1CachedNode408_valid : s1CachedNode408.Valid := ⟨s1CachedNode223_valid,s1CachedNode407_valid⟩

def s1CachedNode409 : CachedPolynomialExpr 9 := .add s1CachedNode227 s1CachedNode236

theorem s1CachedNode409_valid : s1CachedNode409.Valid := ⟨s1CachedNode227_valid,s1CachedNode236_valid⟩

def s1CachedNode410 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode409

theorem s1CachedNode410_valid : s1CachedNode410.Valid := ⟨s1CachedNode2_valid,s1CachedNode409_valid⟩

def s1CachedNode411 : CachedPolynomialExpr 9 := .add s1CachedNode408 s1CachedNode410

theorem s1CachedNode411_valid : s1CachedNode411.Valid := ⟨s1CachedNode408_valid,s1CachedNode410_valid⟩

def s1CachedNode412 : CachedPolynomialExpr 9 := .add s1CachedNode411 s1CachedNode251

theorem s1CachedNode412_valid : s1CachedNode412.Valid := ⟨s1CachedNode411_valid,s1CachedNode251_valid⟩

def s1CachedNode413 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode412

theorem s1CachedNode413_valid : s1CachedNode413.Valid := ⟨s1CachedNode2_valid,s1CachedNode412_valid⟩

def s1CachedNode414 : CachedPolynomialExpr 9 := .add s1CachedNode406 s1CachedNode413

theorem s1CachedNode414_valid : s1CachedNode414.Valid := ⟨s1CachedNode406_valid,s1CachedNode413_valid⟩

def s1CachedNode415 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode27

theorem s1CachedNode415_valid : s1CachedNode415.Valid := ⟨s1CachedNode256_valid,s1CachedNode27_valid⟩

def s1CachedNode416 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode415

theorem s1CachedNode416_valid : s1CachedNode416.Valid := ⟨s1CachedNode255_valid,s1CachedNode415_valid⟩

def s1CachedNode417 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode178

theorem s1CachedNode417_valid : s1CachedNode417.Valid := ⟨s1CachedNode27_valid,s1CachedNode178_valid⟩

def s1CachedNode418 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode321

theorem s1CachedNode418_valid : s1CachedNode418.Valid := ⟨s1CachedNode260_valid,s1CachedNode321_valid⟩

def s1CachedNode419 : CachedPolynomialExpr 9 := .mul s1CachedNode417 s1CachedNode418

theorem s1CachedNode419_valid : s1CachedNode419.Valid := ⟨s1CachedNode417_valid,s1CachedNode418_valid⟩

def s1CachedNode420 : CachedPolynomialExpr 9 := .add s1CachedNode416 s1CachedNode419

theorem s1CachedNode420_valid : s1CachedNode420.Valid := ⟨s1CachedNode416_valid,s1CachedNode419_valid⟩

def s1CachedNode421 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode420

theorem s1CachedNode421_valid : s1CachedNode421.Valid := ⟨s1CachedNode178_valid,s1CachedNode420_valid⟩

def s1CachedNode422 : CachedPolynomialExpr 9 := .add s1CachedNode414 s1CachedNode421

theorem s1CachedNode422_valid : s1CachedNode422.Valid := ⟨s1CachedNode414_valid,s1CachedNode421_valid⟩

def s1CachedNode423 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode422

theorem s1CachedNode423_valid : s1CachedNode423.Valid := ⟨s1CachedNode2_valid,s1CachedNode422_valid⟩

def s1CachedNode424 : CachedPolynomialExpr 9 := .add s1CachedNode404 s1CachedNode423

theorem s1CachedNode424_valid : s1CachedNode424.Valid := ⟨s1CachedNode404_valid,s1CachedNode423_valid⟩

def s1CachedNode425 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode334

theorem s1CachedNode425_valid : s1CachedNode425.Valid := ⟨s1CachedNode27_valid,s1CachedNode334_valid⟩

def s1CachedNode426 : CachedPolynomialExpr 9 := .add s1CachedNode332 s1CachedNode425

theorem s1CachedNode426_valid : s1CachedNode426.Valid := ⟨s1CachedNode332_valid,s1CachedNode425_valid⟩

def s1CachedNode427 : CachedPolynomialExpr 9 := .add s1CachedNode418 s1CachedNode337

theorem s1CachedNode427_valid : s1CachedNode427.Valid := ⟨s1CachedNode418_valid,s1CachedNode337_valid⟩

def s1CachedNode428 : CachedPolynomialExpr 9 := .mul s1CachedNode417 s1CachedNode340

theorem s1CachedNode428_valid : s1CachedNode428.Valid := ⟨s1CachedNode417_valid,s1CachedNode340_valid⟩

def s1CachedNode429 : CachedPolynomialExpr 9 := .add s1CachedNode427 s1CachedNode428

theorem s1CachedNode429_valid : s1CachedNode429.Valid := ⟨s1CachedNode427_valid,s1CachedNode428_valid⟩

def s1CachedNode430 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode429

theorem s1CachedNode430_valid : s1CachedNode430.Valid := ⟨s1CachedNode178_valid,s1CachedNode429_valid⟩

def s1CachedNode431 : CachedPolynomialExpr 9 := .add s1CachedNode426 s1CachedNode430

theorem s1CachedNode431_valid : s1CachedNode431.Valid := ⟨s1CachedNode426_valid,s1CachedNode430_valid⟩

def s1CachedNode432 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode362

theorem s1CachedNode432_valid : s1CachedNode432.Valid := ⟨s1CachedNode4_valid,s1CachedNode362_valid⟩

def s1CachedNode433 : CachedPolynomialExpr 9 := .add s1CachedNode358 s1CachedNode432

theorem s1CachedNode433_valid : s1CachedNode433.Valid := ⟨s1CachedNode358_valid,s1CachedNode432_valid⟩

def s1CachedNode434 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode433

theorem s1CachedNode434_valid : s1CachedNode434.Valid := ⟨s1CachedNode81_valid,s1CachedNode433_valid⟩

def s1CachedNode435 : CachedPolynomialExpr 9 := .add s1CachedNode431 s1CachedNode434

theorem s1CachedNode435_valid : s1CachedNode435.Valid := ⟨s1CachedNode431_valid,s1CachedNode434_valid⟩

def s1CachedNode436 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode435

theorem s1CachedNode436_valid : s1CachedNode436.Valid := ⟨s1CachedNode4_valid,s1CachedNode435_valid⟩

def s1CachedNode437 : CachedPolynomialExpr 9 := .add s1CachedNode424 s1CachedNode436

theorem s1CachedNode437_valid : s1CachedNode437.Valid := ⟨s1CachedNode424_valid,s1CachedNode436_valid⟩

def s1CachedNode438 : CachedPolynomialExpr 9 := .mul s1CachedNode321 s1CachedNode178

theorem s1CachedNode438_valid : s1CachedNode438.Valid := ⟨s1CachedNode321_valid,s1CachedNode178_valid⟩

def s1CachedNode439 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode438

theorem s1CachedNode439_valid : s1CachedNode439.Valid := ⟨s1CachedNode255_valid,s1CachedNode438_valid⟩

def s1CachedNode440 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode439

theorem s1CachedNode440_valid : s1CachedNode440.Valid := ⟨s1CachedNode178_valid,s1CachedNode439_valid⟩

def s1CachedNode441 : CachedPolynomialExpr 9 := .add s1CachedNode437 s1CachedNode440

theorem s1CachedNode441_valid : s1CachedNode441.Valid := ⟨s1CachedNode437_valid,s1CachedNode440_valid⟩

def s1CachedNode442 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode441

theorem s1CachedNode442_valid : s1CachedNode442.Valid := ⟨s1CachedNode2_valid,s1CachedNode441_valid⟩

def s1CachedNode443 : CachedPolynomialExpr 9 := .add s1CachedNode400 s1CachedNode442

theorem s1CachedNode443_valid : s1CachedNode443.Valid := ⟨s1CachedNode400_valid,s1CachedNode442_valid⟩

def s1CachedGradient1 : CachedPolynomialExpr 9 := s1CachedNode443

theorem s1CachedGradient1_valid : s1CachedGradient1.Valid := s1CachedNode443_valid

theorem s1CachedGradient1_erase : s1CachedGradient1.erase = s1HornerGradient1 := by decide +kernel

def s1CachedNode444 : CachedPolynomialExpr 9 := .mul s1CachedNode286 s1CachedNode34

theorem s1CachedNode444_valid : s1CachedNode444.Valid := ⟨s1CachedNode286_valid,s1CachedNode34_valid⟩

def s1CachedNode445 : CachedPolynomialExpr 9 := .add s1CachedNode286 s1CachedNode444

theorem s1CachedNode445_valid : s1CachedNode445.Valid := ⟨s1CachedNode286_valid,s1CachedNode444_valid⟩

def s1CachedNode446 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode445

theorem s1CachedNode446_valid : s1CachedNode446.Valid := ⟨s1CachedNode4_valid,s1CachedNode445_valid⟩

def s1CachedNode447 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode4

theorem s1CachedNode447_valid : s1CachedNode447.Valid := ⟨s1CachedNode1_valid,s1CachedNode4_valid⟩

def s1CachedNode448 : CachedPolynomialExpr 9 := .mul s1CachedNode289 s1CachedNode34

theorem s1CachedNode448_valid : s1CachedNode448.Valid := ⟨s1CachedNode289_valid,s1CachedNode34_valid⟩

def s1CachedNode449 : CachedPolynomialExpr 9 := .add s1CachedNode289 s1CachedNode448

theorem s1CachedNode449_valid : s1CachedNode449.Valid := ⟨s1CachedNode289_valid,s1CachedNode448_valid⟩

def s1CachedNode450 : CachedPolynomialExpr 9 := .mul s1CachedNode447 s1CachedNode449

theorem s1CachedNode450_valid : s1CachedNode450.Valid := ⟨s1CachedNode447_valid,s1CachedNode449_valid⟩

def s1CachedNode451 : CachedPolynomialExpr 9 := .add s1CachedNode446 s1CachedNode450

theorem s1CachedNode451_valid : s1CachedNode451.Valid := ⟨s1CachedNode446_valid,s1CachedNode450_valid⟩

def s1CachedNode452 : CachedPolynomialExpr 9 := .mul s1CachedNode294 s1CachedNode2

theorem s1CachedNode452_valid : s1CachedNode452.Valid := ⟨s1CachedNode294_valid,s1CachedNode2_valid⟩

def s1CachedNode453 : CachedPolynomialExpr 9 := .mul s1CachedNode452 s1CachedNode4

theorem s1CachedNode453_valid : s1CachedNode453.Valid := ⟨s1CachedNode452_valid,s1CachedNode4_valid⟩

def s1CachedNode454 : CachedPolynomialExpr 9 := .mul s1CachedNode453 s1CachedNode47

theorem s1CachedNode454_valid : s1CachedNode454.Valid := ⟨s1CachedNode453_valid,s1CachedNode47_valid⟩

def s1CachedNode455 : CachedPolynomialExpr 9 := .add s1CachedNode451 s1CachedNode454

theorem s1CachedNode455_valid : s1CachedNode455.Valid := ⟨s1CachedNode451_valid,s1CachedNode454_valid⟩

def s1CachedNode456 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode455

theorem s1CachedNode456_valid : s1CachedNode456.Valid := ⟨s1CachedNode1_valid,s1CachedNode455_valid⟩

def s1CachedNode457 : CachedPolynomialExpr 9 := .add s1CachedNode456 s1CachedNode368

theorem s1CachedNode457_valid : s1CachedNode457.Valid := ⟨s1CachedNode456_valid,s1CachedNode368_valid⟩

def s1CachedNode458 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode457

theorem s1CachedNode458_valid : s1CachedNode458.Valid := ⟨s1CachedNode1_valid,s1CachedNode457_valid⟩

def s1CachedNode459 : CachedPolynomialExpr 9 := .add s1CachedNode301 s1CachedNode454

theorem s1CachedNode459_valid : s1CachedNode459.Valid := ⟨s1CachedNode301_valid,s1CachedNode454_valid⟩

def s1CachedNode460 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode459

theorem s1CachedNode460_valid : s1CachedNode460.Valid := ⟨s1CachedNode2_valid,s1CachedNode459_valid⟩

def s1CachedNode461 : CachedPolynomialExpr 9 := .mul s1CachedNode267 s1CachedNode47

theorem s1CachedNode461_valid : s1CachedNode461.Valid := ⟨s1CachedNode267_valid,s1CachedNode47_valid⟩

def s1CachedNode462 : CachedPolynomialExpr 9 := .add s1CachedNode461 s1CachedNode245

theorem s1CachedNode462_valid : s1CachedNode462.Valid := ⟨s1CachedNode461_valid,s1CachedNode245_valid⟩

def s1CachedNode463 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode462

theorem s1CachedNode463_valid : s1CachedNode463.Valid := ⟨s1CachedNode4_valid,s1CachedNode462_valid⟩

def s1CachedNode464 : CachedPolynomialExpr 9 := .add s1CachedNode12 s1CachedNode463

theorem s1CachedNode464_valid : s1CachedNode464.Valid := ⟨s1CachedNode12_valid,s1CachedNode463_valid⟩

def s1CachedNode465 : CachedPolynomialExpr 9 := .add s1CachedNode464 s1CachedNode317

theorem s1CachedNode465_valid : s1CachedNode465.Valid := ⟨s1CachedNode464_valid,s1CachedNode317_valid⟩

def s1CachedNode466 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode465

theorem s1CachedNode466_valid : s1CachedNode466.Valid := ⟨s1CachedNode4_valid,s1CachedNode465_valid⟩

def s1CachedNode467 : CachedPolynomialExpr 9 := .add s1CachedNode460 s1CachedNode466

theorem s1CachedNode467_valid : s1CachedNode467.Valid := ⟨s1CachedNode460_valid,s1CachedNode466_valid⟩

def s1CachedNode468 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode467

theorem s1CachedNode468_valid : s1CachedNode468.Valid := ⟨s1CachedNode2_valid,s1CachedNode467_valid⟩

def s1CachedNode469 : CachedPolynomialExpr 9 := .add s1CachedNode458 s1CachedNode468

theorem s1CachedNode469_valid : s1CachedNode469.Valid := ⟨s1CachedNode458_valid,s1CachedNode468_valid⟩

def s1CachedNode470 : CachedPolynomialExpr 9 := .mul s1CachedNode280 s1CachedNode34

theorem s1CachedNode470_valid : s1CachedNode470.Valid := ⟨s1CachedNode280_valid,s1CachedNode34_valid⟩

def s1CachedNode471 : CachedPolynomialExpr 9 := .add s1CachedNode276 s1CachedNode470

theorem s1CachedNode471_valid : s1CachedNode471.Valid := ⟨s1CachedNode276_valid,s1CachedNode470_valid⟩

def s1CachedNode472 : CachedPolynomialExpr 9 := .add s1CachedNode277 s1CachedNode333

theorem s1CachedNode472_valid : s1CachedNode472.Valid := ⟨s1CachedNode277_valid,s1CachedNode333_valid⟩

def s1CachedNode473 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode472

theorem s1CachedNode473_valid : s1CachedNode473.Valid := ⟨s1CachedNode20_valid,s1CachedNode472_valid⟩

def s1CachedNode474 : CachedPolynomialExpr 9 := .add s1CachedNode471 s1CachedNode473

theorem s1CachedNode474_valid : s1CachedNode474.Valid := ⟨s1CachedNode471_valid,s1CachedNode473_valid⟩

def s1CachedNode475 : CachedPolynomialExpr 9 := .mul s1CachedNode390 s1CachedNode34

theorem s1CachedNode475_valid : s1CachedNode475.Valid := ⟨s1CachedNode390_valid,s1CachedNode34_valid⟩

def s1CachedNode476 : CachedPolynomialExpr 9 := .add s1CachedNode339 s1CachedNode475

theorem s1CachedNode476_valid : s1CachedNode476.Valid := ⟨s1CachedNode339_valid,s1CachedNode475_valid⟩

def s1CachedNode477 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode476

theorem s1CachedNode477_valid : s1CachedNode477.Valid := ⟨s1CachedNode178_valid,s1CachedNode476_valid⟩

def s1CachedNode478 : CachedPolynomialExpr 9 := .add s1CachedNode338 s1CachedNode477

theorem s1CachedNode478_valid : s1CachedNode478.Valid := ⟨s1CachedNode338_valid,s1CachedNode477_valid⟩

def s1CachedNode479 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode478

theorem s1CachedNode479_valid : s1CachedNode479.Valid := ⟨s1CachedNode178_valid,s1CachedNode478_valid⟩

def s1CachedNode480 : CachedPolynomialExpr 9 := .add s1CachedNode474 s1CachedNode479

theorem s1CachedNode480_valid : s1CachedNode480.Valid := ⟨s1CachedNode474_valid,s1CachedNode479_valid⟩

def s1CachedNode481 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode379

theorem s1CachedNode481_valid : s1CachedNode481.Valid := ⟨s1CachedNode4_valid,s1CachedNode379_valid⟩

def s1CachedNode482 : CachedPolynomialExpr 9 := .add s1CachedNode377 s1CachedNode481

theorem s1CachedNode482_valid : s1CachedNode482.Valid := ⟨s1CachedNode377_valid,s1CachedNode481_valid⟩

def s1CachedNode483 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode482

theorem s1CachedNode483_valid : s1CachedNode483.Valid := ⟨s1CachedNode81_valid,s1CachedNode482_valid⟩

def s1CachedNode484 : CachedPolynomialExpr 9 := .add s1CachedNode480 s1CachedNode483

theorem s1CachedNode484_valid : s1CachedNode484.Valid := ⟨s1CachedNode480_valid,s1CachedNode483_valid⟩

def s1CachedNode485 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode484

theorem s1CachedNode485_valid : s1CachedNode485.Valid := ⟨s1CachedNode4_valid,s1CachedNode484_valid⟩

def s1CachedNode486 : CachedPolynomialExpr 9 := .add s1CachedNode469 s1CachedNode485

theorem s1CachedNode486_valid : s1CachedNode486.Valid := ⟨s1CachedNode469_valid,s1CachedNode485_valid⟩

def s1CachedNode487 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode486

theorem s1CachedNode487_valid : s1CachedNode487.Valid := ⟨s1CachedNode1_valid,s1CachedNode486_valid⟩

def s1CachedNode488 : CachedPolynomialExpr 9 := .add s1CachedNode211 s1CachedNode487

theorem s1CachedNode488_valid : s1CachedNode488.Valid := ⟨s1CachedNode211_valid,s1CachedNode487_valid⟩

def s1CachedNode489 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode472

theorem s1CachedNode489_valid : s1CachedNode489.Valid := ⟨s1CachedNode27_valid,s1CachedNode472_valid⟩

def s1CachedNode490 : CachedPolynomialExpr 9 := .add s1CachedNode471 s1CachedNode489

theorem s1CachedNode490_valid : s1CachedNode490.Valid := ⟨s1CachedNode471_valid,s1CachedNode489_valid⟩

def s1CachedNode491 : CachedPolynomialExpr 9 := .mul s1CachedNode323 s1CachedNode34

theorem s1CachedNode491_valid : s1CachedNode491.Valid := ⟨s1CachedNode323_valid,s1CachedNode34_valid⟩

def s1CachedNode492 : CachedPolynomialExpr 9 := .add s1CachedNode339 s1CachedNode491

theorem s1CachedNode492_valid : s1CachedNode492.Valid := ⟨s1CachedNode339_valid,s1CachedNode491_valid⟩

def s1CachedNode493 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode492

theorem s1CachedNode493_valid : s1CachedNode493.Valid := ⟨s1CachedNode178_valid,s1CachedNode492_valid⟩

def s1CachedNode494 : CachedPolynomialExpr 9 := .add s1CachedNode427 s1CachedNode493

theorem s1CachedNode494_valid : s1CachedNode494.Valid := ⟨s1CachedNode427_valid,s1CachedNode493_valid⟩

def s1CachedNode495 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode494

theorem s1CachedNode495_valid : s1CachedNode495.Valid := ⟨s1CachedNode178_valid,s1CachedNode494_valid⟩

def s1CachedNode496 : CachedPolynomialExpr 9 := .add s1CachedNode490 s1CachedNode495

theorem s1CachedNode496_valid : s1CachedNode496.Valid := ⟨s1CachedNode490_valid,s1CachedNode495_valid⟩

def s1CachedNode497 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode231

theorem s1CachedNode497_valid : s1CachedNode497.Valid := ⟨s1CachedNode4_valid,s1CachedNode231_valid⟩

def s1CachedNode498 : CachedPolynomialExpr 9 := .add s1CachedNode243 s1CachedNode497

theorem s1CachedNode498_valid : s1CachedNode498.Valid := ⟨s1CachedNode243_valid,s1CachedNode497_valid⟩

def s1CachedNode499 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode498

theorem s1CachedNode499_valid : s1CachedNode499.Valid := ⟨s1CachedNode81_valid,s1CachedNode498_valid⟩

def s1CachedNode500 : CachedPolynomialExpr 9 := .add s1CachedNode496 s1CachedNode499

theorem s1CachedNode500_valid : s1CachedNode500.Valid := ⟨s1CachedNode496_valid,s1CachedNode499_valid⟩

def s1CachedNode501 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode500

theorem s1CachedNode501_valid : s1CachedNode501.Valid := ⟨s1CachedNode4_valid,s1CachedNode500_valid⟩

def s1CachedNode502 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode4

theorem s1CachedNode502_valid : s1CachedNode502.Valid := ⟨s1CachedNode2_valid,s1CachedNode4_valid⟩

def s1CachedNode503 : CachedPolynomialExpr 9 := .mul s1CachedNode502 s1CachedNode449

theorem s1CachedNode503_valid : s1CachedNode503.Valid := ⟨s1CachedNode502_valid,s1CachedNode449_valid⟩

def s1CachedNode504 : CachedPolynomialExpr 9 := .add s1CachedNode446 s1CachedNode503

theorem s1CachedNode504_valid : s1CachedNode504.Valid := ⟨s1CachedNode446_valid,s1CachedNode503_valid⟩

def s1CachedNode505 : CachedPolynomialExpr 9 := .mul s1CachedNode77 s1CachedNode504

theorem s1CachedNode505_valid : s1CachedNode505.Valid := ⟨s1CachedNode77_valid,s1CachedNode504_valid⟩

def s1CachedNode506 : CachedPolynomialExpr 9 := .add s1CachedNode501 s1CachedNode505

theorem s1CachedNode506_valid : s1CachedNode506.Valid := ⟨s1CachedNode501_valid,s1CachedNode505_valid⟩

def s1CachedNode507 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode506

theorem s1CachedNode507_valid : s1CachedNode507.Valid := ⟨s1CachedNode2_valid,s1CachedNode506_valid⟩

def s1CachedNode508 : CachedPolynomialExpr 9 := .add s1CachedNode488 s1CachedNode507

theorem s1CachedNode508_valid : s1CachedNode508.Valid := ⟨s1CachedNode488_valid,s1CachedNode507_valid⟩

def s1CachedNode509 : CachedPolynomialExpr 9 := .mul s1CachedNode214 s1CachedNode34

theorem s1CachedNode509_valid : s1CachedNode509.Valid := ⟨s1CachedNode214_valid,s1CachedNode34_valid⟩

def s1CachedNode510 : CachedPolynomialExpr 9 := .add s1CachedNode213 s1CachedNode509

theorem s1CachedNode510_valid : s1CachedNode510.Valid := ⟨s1CachedNode213_valid,s1CachedNode509_valid⟩

def s1CachedNode511 : CachedPolynomialExpr 9 := .mul s1CachedNode34 s1CachedNode510

theorem s1CachedNode511_valid : s1CachedNode511.Valid := ⟨s1CachedNode34_valid,s1CachedNode510_valid⟩

def s1CachedNode512 : CachedPolynomialExpr 9 := .add s1CachedNode212 s1CachedNode511

theorem s1CachedNode512_valid : s1CachedNode512.Valid := ⟨s1CachedNode212_valid,s1CachedNode511_valid⟩

def s1CachedNode513 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode34

theorem s1CachedNode513_valid : s1CachedNode513.Valid := ⟨s1CachedNode220_valid,s1CachedNode34_valid⟩

def s1CachedNode514 : CachedPolynomialExpr 9 := .add s1CachedNode219 s1CachedNode513

theorem s1CachedNode514_valid : s1CachedNode514.Valid := ⟨s1CachedNode219_valid,s1CachedNode513_valid⟩

def s1CachedNode515 : CachedPolynomialExpr 9 := .mul s1CachedNode227 s1CachedNode4

theorem s1CachedNode515_valid : s1CachedNode515.Valid := ⟨s1CachedNode227_valid,s1CachedNode4_valid⟩

def s1CachedNode516 : CachedPolynomialExpr 9 := .add s1CachedNode223 s1CachedNode515

theorem s1CachedNode516_valid : s1CachedNode516.Valid := ⟨s1CachedNode223_valid,s1CachedNode515_valid⟩

def s1CachedNode517 : CachedPolynomialExpr 9 := .mul s1CachedNode224 s1CachedNode34

theorem s1CachedNode517_valid : s1CachedNode517.Valid := ⟨s1CachedNode224_valid,s1CachedNode34_valid⟩

def s1CachedNode518 : CachedPolynomialExpr 9 := .add s1CachedNode516 s1CachedNode517

theorem s1CachedNode518_valid : s1CachedNode518.Valid := ⟨s1CachedNode516_valid,s1CachedNode517_valid⟩

def s1CachedNode519 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode518

theorem s1CachedNode519_valid : s1CachedNode519.Valid := ⟨s1CachedNode4_valid,s1CachedNode518_valid⟩

def s1CachedNode520 : CachedPolynomialExpr 9 := .add s1CachedNode514 s1CachedNode519

theorem s1CachedNode520_valid : s1CachedNode520.Valid := ⟨s1CachedNode514_valid,s1CachedNode519_valid⟩

def s1CachedNode521 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode34

theorem s1CachedNode521_valid : s1CachedNode521.Valid := ⟨s1CachedNode256_valid,s1CachedNode34_valid⟩

def s1CachedNode522 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode521

theorem s1CachedNode522_valid : s1CachedNode522.Valid := ⟨s1CachedNode255_valid,s1CachedNode521_valid⟩

def s1CachedNode523 : CachedPolynomialExpr 9 := .mul s1CachedNode34 s1CachedNode178

theorem s1CachedNode523_valid : s1CachedNode523.Valid := ⟨s1CachedNode34_valid,s1CachedNode178_valid⟩

def s1CachedNode524 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode337

theorem s1CachedNode524_valid : s1CachedNode524.Valid := ⟨s1CachedNode260_valid,s1CachedNode337_valid⟩

def s1CachedNode525 : CachedPolynomialExpr 9 := .mul s1CachedNode523 s1CachedNode524

theorem s1CachedNode525_valid : s1CachedNode525.Valid := ⟨s1CachedNode523_valid,s1CachedNode524_valid⟩

def s1CachedNode526 : CachedPolynomialExpr 9 := .add s1CachedNode522 s1CachedNode525

theorem s1CachedNode526_valid : s1CachedNode526.Valid := ⟨s1CachedNode522_valid,s1CachedNode525_valid⟩

def s1CachedNode527 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode526

theorem s1CachedNode527_valid : s1CachedNode527.Valid := ⟨s1CachedNode178_valid,s1CachedNode526_valid⟩

def s1CachedNode528 : CachedPolynomialExpr 9 := .add s1CachedNode520 s1CachedNode527

theorem s1CachedNode528_valid : s1CachedNode528.Valid := ⟨s1CachedNode520_valid,s1CachedNode527_valid⟩

def s1CachedNode529 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode528

theorem s1CachedNode529_valid : s1CachedNode529.Valid := ⟨s1CachedNode4_valid,s1CachedNode528_valid⟩

def s1CachedNode530 : CachedPolynomialExpr 9 := .add s1CachedNode512 s1CachedNode529

theorem s1CachedNode530_valid : s1CachedNode530.Valid := ⟨s1CachedNode512_valid,s1CachedNode529_valid⟩

def s1CachedNode531 : CachedPolynomialExpr 9 := .mul s1CachedNode337 s1CachedNode178

theorem s1CachedNode531_valid : s1CachedNode531.Valid := ⟨s1CachedNode337_valid,s1CachedNode178_valid⟩

def s1CachedNode532 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode531

theorem s1CachedNode532_valid : s1CachedNode532.Valid := ⟨s1CachedNode255_valid,s1CachedNode531_valid⟩

def s1CachedNode533 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode532

theorem s1CachedNode533_valid : s1CachedNode533.Valid := ⟨s1CachedNode178_valid,s1CachedNode532_valid⟩

def s1CachedNode534 : CachedPolynomialExpr 9 := .add s1CachedNode530 s1CachedNode533

theorem s1CachedNode534_valid : s1CachedNode534.Valid := ⟨s1CachedNode530_valid,s1CachedNode533_valid⟩

def s1CachedNode535 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode534

theorem s1CachedNode535_valid : s1CachedNode535.Valid := ⟨s1CachedNode4_valid,s1CachedNode534_valid⟩

def s1CachedNode536 : CachedPolynomialExpr 9 := .add s1CachedNode508 s1CachedNode535

theorem s1CachedNode536_valid : s1CachedNode536.Valid := ⟨s1CachedNode508_valid,s1CachedNode535_valid⟩

def s1CachedGradient2 : CachedPolynomialExpr 9 := s1CachedNode536

theorem s1CachedGradient2_valid : s1CachedGradient2.Valid := s1CachedNode536_valid

theorem s1CachedGradient2_erase : s1CachedGradient2.erase = s1HornerGradient2 := by decide +kernel

def s1CachedNode537 : CachedPolynomialExpr 9 := .rational (-1300872433938791506499202187661275/973555660975280180349468061728768 : ℚ) ⟨-1540542430142948531,-1540542430142948530⟩

theorem s1CachedNode537_valid : s1CachedNode537.Valid := by decide +kernel

def s1CachedNode538 : CachedPolynomialExpr 9 := .rational (67501818664894582187747550316751/81129638414606681695789005144064 : ℚ) ⟨959258538058727796,959258538058727797⟩

theorem s1CachedNode538_valid : s1CachedNode538.Valid := by decide +kernel

def s1CachedNode539 : CachedPolynomialExpr 9 := .add s1CachedNode538 s1CachedNode311

theorem s1CachedNode539_valid : s1CachedNode539.Valid := ⟨s1CachedNode538_valid,s1CachedNode311_valid⟩

def s1CachedNode540 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode539

theorem s1CachedNode540_valid : s1CachedNode540.Valid := ⟨s1CachedNode20_valid,s1CachedNode539_valid⟩

def s1CachedNode541 : CachedPolynomialExpr 9 := .add s1CachedNode537 s1CachedNode540

theorem s1CachedNode541_valid : s1CachedNode541.Valid := ⟨s1CachedNode537_valid,s1CachedNode540_valid⟩

def s1CachedNode542 : CachedPolynomialExpr 9 := .rational (-1050185586039035/422212465065984 : ℚ) ⟨-2867706773610591574,-2867706773610591573⟩

theorem s1CachedNode542_valid : s1CachedNode542.Valid := by decide +kernel

def s1CachedNode543 : CachedPolynomialExpr 9 := .rational (1019507261509151/844424930131968 : ℚ) ⟨1391967247713827498,1391967247713827499⟩

theorem s1CachedNode543_valid : s1CachedNode543.Valid := by decide +kernel

def s1CachedNode544 : CachedPolynomialExpr 9 := .mul s1CachedNode543 s1CachedNode20

theorem s1CachedNode544_valid : s1CachedNode544.Valid := ⟨s1CachedNode543_valid,s1CachedNode20_valid⟩

def s1CachedNode545 : CachedPolynomialExpr 9 := .add s1CachedNode542 s1CachedNode544

theorem s1CachedNode545_valid : s1CachedNode545.Valid := ⟨s1CachedNode542_valid,s1CachedNode544_valid⟩

def s1CachedNode546 : CachedPolynomialExpr 9 := .rational (-62368855132035964900266565910173/324518553658426726783156020576256 : ℚ) ⟨-221578684758710995,-221578684758710994⟩

theorem s1CachedNode546_valid : s1CachedNode546.Valid := by decide +kernel

def s1CachedNode547 : CachedPolynomialExpr 9 := .rational (-21598566773640891/9007199254740992 : ℚ) ⟨-2764616547026034048,-2764616547026034048⟩

theorem s1CachedNode547_valid : s1CachedNode547.Valid := by decide +kernel

def s1CachedNode548 : CachedPolynomialExpr 9 := .mul s1CachedNode547 s1CachedNode20

theorem s1CachedNode548_valid : s1CachedNode548.Valid := ⟨s1CachedNode547_valid,s1CachedNode20_valid⟩

def s1CachedNode549 : CachedPolynomialExpr 9 := .add s1CachedNode546 s1CachedNode548

theorem s1CachedNode549_valid : s1CachedNode549.Valid := ⟨s1CachedNode546_valid,s1CachedNode548_valid⟩

def s1CachedNode550 : CachedPolynomialExpr 9 := .rational (187820197371309106883475032631535/30423614405477505635920876929024 : ℚ) ⟨7117561433131304014,7117561433131304015⟩

theorem s1CachedNode550_valid : s1CachedNode550.Valid := by decide +kernel

def s1CachedNode551 : CachedPolynomialExpr 9 := .rational (-6881924343606227/844424930131968 : ℚ) ⟨-9396120703803701931,-9396120703803701930⟩

theorem s1CachedNode551_valid : s1CachedNode551.Valid := by decide +kernel

def s1CachedNode552 : CachedPolynomialExpr 9 := .rational (-6881924343606227/1688849860263936 : ℚ) ⟨-4698060351901850966,-4698060351901850965⟩

theorem s1CachedNode552_valid : s1CachedNode552.Valid := by decide +kernel

def s1CachedNode553 : CachedPolynomialExpr 9 := .mul s1CachedNode552 s1CachedNode27

theorem s1CachedNode553_valid : s1CachedNode553.Valid := ⟨s1CachedNode552_valid,s1CachedNode27_valid⟩

def s1CachedNode554 : CachedPolynomialExpr 9 := .add s1CachedNode551 s1CachedNode553

theorem s1CachedNode554_valid : s1CachedNode554.Valid := ⟨s1CachedNode551_valid,s1CachedNode553_valid⟩

def s1CachedNode555 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode554

theorem s1CachedNode555_valid : s1CachedNode555.Valid := ⟨s1CachedNode2_valid,s1CachedNode554_valid⟩

def s1CachedNode556 : CachedPolynomialExpr 9 := .add s1CachedNode550 s1CachedNode555

theorem s1CachedNode556_valid : s1CachedNode556.Valid := ⟨s1CachedNode550_valid,s1CachedNode555_valid⟩

def s1CachedNode557 : CachedPolynomialExpr 9 := .mul s1CachedNode552 s1CachedNode34

theorem s1CachedNode557_valid : s1CachedNode557.Valid := ⟨s1CachedNode552_valid,s1CachedNode34_valid⟩

def s1CachedNode558 : CachedPolynomialExpr 9 := .add s1CachedNode551 s1CachedNode557

theorem s1CachedNode558_valid : s1CachedNode558.Valid := ⟨s1CachedNode551_valid,s1CachedNode557_valid⟩

def s1CachedNode559 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode558

theorem s1CachedNode559_valid : s1CachedNode559.Valid := ⟨s1CachedNode4_valid,s1CachedNode558_valid⟩

def s1CachedNode560 : CachedPolynomialExpr 9 := .add s1CachedNode556 s1CachedNode559

theorem s1CachedNode560_valid : s1CachedNode560.Valid := ⟨s1CachedNode556_valid,s1CachedNode559_valid⟩

def s1CachedNode561 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode560

theorem s1CachedNode561_valid : s1CachedNode561.Valid := ⟨s1CachedNode1_valid,s1CachedNode560_valid⟩

def s1CachedNode562 : CachedPolynomialExpr 9 := .add s1CachedNode549 s1CachedNode561

theorem s1CachedNode562_valid : s1CachedNode562.Valid := ⟨s1CachedNode549_valid,s1CachedNode561_valid⟩

def s1CachedNode563 : CachedPolynomialExpr 9 := .rational (21293898337211913/9007199254740992 : ℚ) ⟨2725618987163124864,2725618987163124864⟩

theorem s1CachedNode563_valid : s1CachedNode563.Valid := by decide +kernel

def s1CachedNode564 : CachedPolynomialExpr 9 := .rational (21293898337211913/18014398509481984 : ℚ) ⟨1362809493581562432,1362809493581562432⟩

theorem s1CachedNode564_valid : s1CachedNode564.Valid := by decide +kernel

def s1CachedNode565 : CachedPolynomialExpr 9 := .mul s1CachedNode564 s1CachedNode27

theorem s1CachedNode565_valid : s1CachedNode565.Valid := ⟨s1CachedNode564_valid,s1CachedNode27_valid⟩

def s1CachedNode566 : CachedPolynomialExpr 9 := .add s1CachedNode563 s1CachedNode565

theorem s1CachedNode566_valid : s1CachedNode566.Valid := ⟨s1CachedNode563_valid,s1CachedNode565_valid⟩

def s1CachedNode567 : CachedPolynomialExpr 9 := .rational (21598566773640891/9007199254740992 : ℚ) ⟨2764616547026034048,2764616547026034048⟩

theorem s1CachedNode567_valid : s1CachedNode567.Valid := by decide +kernel

def s1CachedNode568 : CachedPolynomialExpr 9 := .mul s1CachedNode567 s1CachedNode4

theorem s1CachedNode568_valid : s1CachedNode568.Valid := ⟨s1CachedNode567_valid,s1CachedNode4_valid⟩

def s1CachedNode569 : CachedPolynomialExpr 9 := .mul s1CachedNode568 s1CachedNode47

theorem s1CachedNode569_valid : s1CachedNode569.Valid := ⟨s1CachedNode568_valid,s1CachedNode47_valid⟩

def s1CachedNode570 : CachedPolynomialExpr 9 := .add s1CachedNode566 s1CachedNode569

theorem s1CachedNode570_valid : s1CachedNode570.Valid := ⟨s1CachedNode566_valid,s1CachedNode569_valid⟩

def s1CachedNode571 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode570

theorem s1CachedNode571_valid : s1CachedNode571.Valid := ⟨s1CachedNode2_valid,s1CachedNode570_valid⟩

def s1CachedNode572 : CachedPolynomialExpr 9 := .add s1CachedNode562 s1CachedNode571

theorem s1CachedNode572_valid : s1CachedNode572.Valid := ⟨s1CachedNode562_valid,s1CachedNode571_valid⟩

def s1CachedNode573 : CachedPolynomialExpr 9 := .mul s1CachedNode564 s1CachedNode34

theorem s1CachedNode573_valid : s1CachedNode573.Valid := ⟨s1CachedNode564_valid,s1CachedNode34_valid⟩

def s1CachedNode574 : CachedPolynomialExpr 9 := .add s1CachedNode563 s1CachedNode573

theorem s1CachedNode574_valid : s1CachedNode574.Valid := ⟨s1CachedNode563_valid,s1CachedNode573_valid⟩

def s1CachedNode575 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode574

theorem s1CachedNode575_valid : s1CachedNode575.Valid := ⟨s1CachedNode4_valid,s1CachedNode574_valid⟩

def s1CachedNode576 : CachedPolynomialExpr 9 := .add s1CachedNode572 s1CachedNode575

theorem s1CachedNode576_valid : s1CachedNode576.Valid := ⟨s1CachedNode572_valid,s1CachedNode575_valid⟩

def s1CachedNode577 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode576

theorem s1CachedNode577_valid : s1CachedNode577.Valid := ⟨s1CachedNode1_valid,s1CachedNode576_valid⟩

def s1CachedNode578 : CachedPolynomialExpr 9 := .add s1CachedNode545 s1CachedNode577

theorem s1CachedNode578_valid : s1CachedNode578.Valid := ⟨s1CachedNode545_valid,s1CachedNode577_valid⟩

def s1CachedNode579 : CachedPolynomialExpr 9 := .rational (1080863910568919/422212465065984 : ℚ) ⟨2951479051793528149,2951479051793528150⟩

theorem s1CachedNode579_valid : s1CachedNode579.Valid := by decide +kernel

def s1CachedNode580 : CachedPolynomialExpr 9 := .mul s1CachedNode579 s1CachedNode20

theorem s1CachedNode580_valid : s1CachedNode580.Valid := ⟨s1CachedNode579_valid,s1CachedNode20_valid⟩

def s1CachedNode581 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode20

theorem s1CachedNode581_valid : s1CachedNode581.Valid := ⟨s1CachedNode25_valid,s1CachedNode20_valid⟩

def s1CachedNode582 : CachedPolynomialExpr 9 := .mul s1CachedNode581 s1CachedNode20

theorem s1CachedNode582_valid : s1CachedNode582.Valid := ⟨s1CachedNode581_valid,s1CachedNode20_valid⟩

def s1CachedNode583 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode582

theorem s1CachedNode583_valid : s1CachedNode583.Valid := ⟨s1CachedNode256_valid,s1CachedNode582_valid⟩

def s1CachedNode584 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode583

theorem s1CachedNode584_valid : s1CachedNode584.Valid := ⟨s1CachedNode260_valid,s1CachedNode583_valid⟩

def s1CachedNode585 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode584

theorem s1CachedNode585_valid : s1CachedNode585.Valid := ⟨s1CachedNode178_valid,s1CachedNode584_valid⟩

def s1CachedNode586 : CachedPolynomialExpr 9 := .add s1CachedNode580 s1CachedNode585

theorem s1CachedNode586_valid : s1CachedNode586.Valid := ⟨s1CachedNode580_valid,s1CachedNode585_valid⟩

def s1CachedNode587 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode586

theorem s1CachedNode587_valid : s1CachedNode587.Valid := ⟨s1CachedNode178_valid,s1CachedNode586_valid⟩

def s1CachedNode588 : CachedPolynomialExpr 9 := .add s1CachedNode578 s1CachedNode587

theorem s1CachedNode588_valid : s1CachedNode588.Valid := ⟨s1CachedNode578_valid,s1CachedNode587_valid⟩

def s1CachedNode589 : CachedPolynomialExpr 9 := .rational (-1019507261509151/844424930131968 : ℚ) ⟨-1391967247713827499,-1391967247713827498⟩

theorem s1CachedNode589_valid : s1CachedNode589.Valid := by decide +kernel

def s1CachedNode590 : CachedPolynomialExpr 9 := .mul s1CachedNode589 s1CachedNode2

theorem s1CachedNode590_valid : s1CachedNode590.Valid := ⟨s1CachedNode589_valid,s1CachedNode2_valid⟩

def s1CachedNode591 : CachedPolynomialExpr 9 := .mul s1CachedNode590 s1CachedNode4

theorem s1CachedNode591_valid : s1CachedNode591.Valid := ⟨s1CachedNode590_valid,s1CachedNode4_valid⟩

def s1CachedNode592 : CachedPolynomialExpr 9 := .mul s1CachedNode591 s1CachedNode47

theorem s1CachedNode592_valid : s1CachedNode592.Valid := ⟨s1CachedNode591_valid,s1CachedNode47_valid⟩

def s1CachedNode593 : CachedPolynomialExpr 9 := .add s1CachedNode588 s1CachedNode592

theorem s1CachedNode593_valid : s1CachedNode593.Valid := ⟨s1CachedNode588_valid,s1CachedNode592_valid⟩

def s1CachedNode594 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode593

theorem s1CachedNode594_valid : s1CachedNode594.Valid := ⟨s1CachedNode1_valid,s1CachedNode593_valid⟩

def s1CachedNode595 : CachedPolynomialExpr 9 := .add s1CachedNode541 s1CachedNode594

theorem s1CachedNode595_valid : s1CachedNode595.Valid := ⟨s1CachedNode541_valid,s1CachedNode594_valid⟩

def s1CachedNode596 : CachedPolynomialExpr 9 := .rational (41607685414015231/27021597764222976 : ℚ) ⟨1775261244331316522,1775261244331316523⟩

theorem s1CachedNode596_valid : s1CachedNode596.Valid := by decide +kernel

def s1CachedNode597 : CachedPolynomialExpr 9 := .rational (7541973450629039/110680464442257309696 : ℚ) ⟨78562223444052,78562223444053⟩

theorem s1CachedNode597_valid : s1CachedNode597.Valid := by decide +kernel

def s1CachedNode598 : CachedPolynomialExpr 9 := .mul s1CachedNode597 s1CachedNode47

theorem s1CachedNode598_valid : s1CachedNode598.Valid := ⟨s1CachedNode597_valid,s1CachedNode47_valid⟩

def s1CachedNode599 : CachedPolynomialExpr 9 := .add s1CachedNode596 s1CachedNode598

theorem s1CachedNode599_valid : s1CachedNode599.Valid := ⟨s1CachedNode596_valid,s1CachedNode598_valid⟩

def s1CachedNode600 : CachedPolynomialExpr 9 := .rational (24313862844912527/54043195528445952 : ℚ) ⟨518695740691467242,518695740691467243⟩

theorem s1CachedNode600_valid : s1CachedNode600.Valid := by decide +kernel

def s1CachedNode601 : CachedPolynomialExpr 9 := .mul s1CachedNode600 s1CachedNode27

theorem s1CachedNode601_valid : s1CachedNode601.Valid := ⟨s1CachedNode600_valid,s1CachedNode27_valid⟩

def s1CachedNode602 : CachedPolynomialExpr 9 := .add s1CachedNode599 s1CachedNode601

theorem s1CachedNode602_valid : s1CachedNode602.Valid := ⟨s1CachedNode599_valid,s1CachedNode601_valid⟩

def s1CachedNode603 : CachedPolynomialExpr 9 := .rational (-29356921275348481/54043195528445952 : ℚ) ⟨-626280987207434262,-626280987207434261⟩

theorem s1CachedNode603_valid : s1CachedNode603.Valid := by decide +kernel

def s1CachedNode604 : CachedPolynomialExpr 9 := .rational (-1118141335838771/2251799813685248 : ℚ) ⟨-572488363949450752,-572488363949450752⟩

theorem s1CachedNode604_valid : s1CachedNode604.Valid := by decide +kernel

def s1CachedNode605 : CachedPolynomialExpr 9 := .mul s1CachedNode604 s1CachedNode27

theorem s1CachedNode605_valid : s1CachedNode605.Valid := ⟨s1CachedNode604_valid,s1CachedNode27_valid⟩

def s1CachedNode606 : CachedPolynomialExpr 9 := .add s1CachedNode603 s1CachedNode605

theorem s1CachedNode606_valid : s1CachedNode606.Valid := ⟨s1CachedNode603_valid,s1CachedNode605_valid⟩

def s1CachedNode607 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode606

theorem s1CachedNode607_valid : s1CachedNode607.Valid := ⟨s1CachedNode20_valid,s1CachedNode606_valid⟩

def s1CachedNode608 : CachedPolynomialExpr 9 := .add s1CachedNode602 s1CachedNode607

theorem s1CachedNode608_valid : s1CachedNode608.Valid := ⟨s1CachedNode602_valid,s1CachedNode607_valid⟩

def s1CachedNode609 : CachedPolynomialExpr 9 := .rational (2365988704134657/18014398509481984 : ℚ) ⟨151423277064618048,151423277064618048⟩

theorem s1CachedNode609_valid : s1CachedNode609.Valid := by decide +kernel

def s1CachedNode610 : CachedPolynomialExpr 9 := .mul s1CachedNode609 s1CachedNode20

theorem s1CachedNode610_valid : s1CachedNode610.Valid := ⟨s1CachedNode609_valid,s1CachedNode20_valid⟩

def s1CachedNode611 : CachedPolynomialExpr 9 := .rational (-6881924343606227/27021597764222976 : ℚ) ⟨-293628771993865686,-293628771993865685⟩

theorem s1CachedNode611_valid : s1CachedNode611.Valid := by decide +kernel

def s1CachedNode612 : CachedPolynomialExpr 9 := .mul s1CachedNode611 s1CachedNode20

theorem s1CachedNode612_valid : s1CachedNode612.Valid := ⟨s1CachedNode611_valid,s1CachedNode20_valid⟩

def s1CachedNode613 : CachedPolynomialExpr 9 := .mul s1CachedNode612 s1CachedNode2

theorem s1CachedNode613_valid : s1CachedNode613.Valid := ⟨s1CachedNode612_valid,s1CachedNode2_valid⟩

def s1CachedNode614 : CachedPolynomialExpr 9 := .add s1CachedNode610 s1CachedNode613

theorem s1CachedNode614_valid : s1CachedNode614.Valid := ⟨s1CachedNode610_valid,s1CachedNode613_valid⟩

def s1CachedNode615 : CachedPolynomialExpr 9 := .rational (7199522257880297/27021597764222976 : ℚ) ⟨307179616336226005,307179616336226006⟩

theorem s1CachedNode615_valid : s1CachedNode615.Valid := by decide +kernel

def s1CachedNode616 : CachedPolynomialExpr 9 := .mul s1CachedNode615 s1CachedNode4

theorem s1CachedNode616_valid : s1CachedNode616.Valid := ⟨s1CachedNode615_valid,s1CachedNode4_valid⟩

def s1CachedNode617 : CachedPolynomialExpr 9 := .mul s1CachedNode616 s1CachedNode47

theorem s1CachedNode617_valid : s1CachedNode617.Valid := ⟨s1CachedNode616_valid,s1CachedNode47_valid⟩

def s1CachedNode618 : CachedPolynomialExpr 9 := .add s1CachedNode614 s1CachedNode617

theorem s1CachedNode618_valid : s1CachedNode618.Valid := ⟨s1CachedNode614_valid,s1CachedNode617_valid⟩

def s1CachedNode619 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode618

theorem s1CachedNode619_valid : s1CachedNode619.Valid := ⟨s1CachedNode2_valid,s1CachedNode618_valid⟩

def s1CachedNode620 : CachedPolynomialExpr 9 := .rational (-1019507261509151/3377699720527872 : ℚ) ⟨-347991811928456875,-347991811928456874⟩

theorem s1CachedNode620_valid : s1CachedNode620.Valid := by decide +kernel

def s1CachedNode621 : CachedPolynomialExpr 9 := .mul s1CachedNode620 s1CachedNode4

theorem s1CachedNode621_valid : s1CachedNode621.Valid := ⟨s1CachedNode620_valid,s1CachedNode4_valid⟩

def s1CachedNode622 : CachedPolynomialExpr 9 := .mul s1CachedNode621 s1CachedNode47

theorem s1CachedNode622_valid : s1CachedNode622.Valid := ⟨s1CachedNode621_valid,s1CachedNode47_valid⟩

def s1CachedNode623 : CachedPolynomialExpr 9 := .add s1CachedNode619 s1CachedNode622

theorem s1CachedNode623_valid : s1CachedNode623.Valid := ⟨s1CachedNode619_valid,s1CachedNode622_valid⟩

def s1CachedNode624 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode623

theorem s1CachedNode624_valid : s1CachedNode624.Valid := ⟨s1CachedNode2_valid,s1CachedNode623_valid⟩

def s1CachedNode625 : CachedPolynomialExpr 9 := .add s1CachedNode608 s1CachedNode624

theorem s1CachedNode625_valid : s1CachedNode625.Valid := ⟨s1CachedNode608_valid,s1CachedNode624_valid⟩

def s1CachedNode626 : CachedPolynomialExpr 9 := .rational (2657272677596523/562949953421312 : ℚ) ⟨5442094443717679104,5442094443717679104⟩

theorem s1CachedNode626_valid : s1CachedNode626.Valid := by decide +kernel

def s1CachedNode627 : CachedPolynomialExpr 9 := .mul s1CachedNode620 s1CachedNode47

theorem s1CachedNode627_valid : s1CachedNode627.Valid := ⟨s1CachedNode620_valid,s1CachedNode47_valid⟩

def s1CachedNode628 : CachedPolynomialExpr 9 := .add s1CachedNode627 s1CachedNode617

theorem s1CachedNode628_valid : s1CachedNode628.Valid := ⟨s1CachedNode627_valid,s1CachedNode617_valid⟩

def s1CachedNode629 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode628

theorem s1CachedNode629_valid : s1CachedNode629.Valid := ⟨s1CachedNode4_valid,s1CachedNode628_valid⟩

def s1CachedNode630 : CachedPolynomialExpr 9 := .add s1CachedNode626 s1CachedNode629

theorem s1CachedNode630_valid : s1CachedNode630.Valid := ⟨s1CachedNode626_valid,s1CachedNode629_valid⟩

def s1CachedNode631 : CachedPolynomialExpr 9 := .rational (8264138585216027/216172782113783808 : ℚ) ⟨44075405787818810,44075405787818811⟩

theorem s1CachedNode631_valid : s1CachedNode631.Valid := by decide +kernel

def s1CachedNode632 : CachedPolynomialExpr 9 := .add s1CachedNode631 s1CachedNode215

theorem s1CachedNode632_valid : s1CachedNode632.Valid := ⟨s1CachedNode631_valid,s1CachedNode215_valid⟩

def s1CachedNode633 : CachedPolynomialExpr 9 := .add s1CachedNode632 s1CachedNode401

theorem s1CachedNode633_valid : s1CachedNode633.Valid := ⟨s1CachedNode632_valid,s1CachedNode401_valid⟩

def s1CachedNode634 : CachedPolynomialExpr 9 := .add s1CachedNode633 s1CachedNode509

theorem s1CachedNode634_valid : s1CachedNode634.Valid := ⟨s1CachedNode633_valid,s1CachedNode509_valid⟩

def s1CachedNode635 : CachedPolynomialExpr 9 := .mul s1CachedNode47 s1CachedNode634

theorem s1CachedNode635_valid : s1CachedNode635.Valid := ⟨s1CachedNode47_valid,s1CachedNode634_valid⟩

def s1CachedNode636 : CachedPolynomialExpr 9 := .add s1CachedNode630 s1CachedNode635

theorem s1CachedNode636_valid : s1CachedNode636.Valid := ⟨s1CachedNode630_valid,s1CachedNode635_valid⟩

def s1CachedNode637 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode636

theorem s1CachedNode637_valid : s1CachedNode637.Valid := ⟨s1CachedNode4_valid,s1CachedNode636_valid⟩

def s1CachedNode638 : CachedPolynomialExpr 9 := .add s1CachedNode625 s1CachedNode637

theorem s1CachedNode638_valid : s1CachedNode638.Valid := ⟨s1CachedNode625_valid,s1CachedNode637_valid⟩

def s1CachedNode639 : CachedPolynomialExpr 9 := .add s1CachedNode390 s1CachedNode323

theorem s1CachedNode639_valid : s1CachedNode639.Valid := ⟨s1CachedNode390_valid,s1CachedNode323_valid⟩

def s1CachedNode640 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode418

theorem s1CachedNode640_valid : s1CachedNode640.Valid := ⟨s1CachedNode20_valid,s1CachedNode418_valid⟩

def s1CachedNode641 : CachedPolynomialExpr 9 := .add s1CachedNode324 s1CachedNode640

theorem s1CachedNode641_valid : s1CachedNode641.Valid := ⟨s1CachedNode324_valid,s1CachedNode640_valid⟩

def s1CachedNode642 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode641

theorem s1CachedNode642_valid : s1CachedNode642.Valid := ⟨s1CachedNode178_valid,s1CachedNode641_valid⟩

def s1CachedNode643 : CachedPolynomialExpr 9 := .add s1CachedNode639 s1CachedNode642

theorem s1CachedNode643_valid : s1CachedNode643.Valid := ⟨s1CachedNode639_valid,s1CachedNode642_valid⟩

def s1CachedNode644 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode643

theorem s1CachedNode644_valid : s1CachedNode644.Valid := ⟨s1CachedNode178_valid,s1CachedNode643_valid⟩

def s1CachedNode645 : CachedPolynomialExpr 9 := .add s1CachedNode638 s1CachedNode644

theorem s1CachedNode645_valid : s1CachedNode645.Valid := ⟨s1CachedNode638_valid,s1CachedNode644_valid⟩

def s1CachedNode646 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode645

theorem s1CachedNode646_valid : s1CachedNode646.Valid := ⟨s1CachedNode2_valid,s1CachedNode645_valid⟩

def s1CachedNode647 : CachedPolynomialExpr 9 := .add s1CachedNode595 s1CachedNode646

theorem s1CachedNode647_valid : s1CachedNode647.Valid := ⟨s1CachedNode595_valid,s1CachedNode646_valid⟩

def s1CachedNode648 : CachedPolynomialExpr 9 := .mul s1CachedNode600 s1CachedNode34

theorem s1CachedNode648_valid : s1CachedNode648.Valid := ⟨s1CachedNode600_valid,s1CachedNode34_valid⟩

def s1CachedNode649 : CachedPolynomialExpr 9 := .add s1CachedNode599 s1CachedNode648

theorem s1CachedNode649_valid : s1CachedNode649.Valid := ⟨s1CachedNode599_valid,s1CachedNode648_valid⟩

def s1CachedNode650 : CachedPolynomialExpr 9 := .mul s1CachedNode604 s1CachedNode34

theorem s1CachedNode650_valid : s1CachedNode650.Valid := ⟨s1CachedNode604_valid,s1CachedNode34_valid⟩

def s1CachedNode651 : CachedPolynomialExpr 9 := .add s1CachedNode603 s1CachedNode650

theorem s1CachedNode651_valid : s1CachedNode651.Valid := ⟨s1CachedNode603_valid,s1CachedNode650_valid⟩

def s1CachedNode652 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode651

theorem s1CachedNode652_valid : s1CachedNode652.Valid := ⟨s1CachedNode20_valid,s1CachedNode651_valid⟩

def s1CachedNode653 : CachedPolynomialExpr 9 := .add s1CachedNode649 s1CachedNode652

theorem s1CachedNode653_valid : s1CachedNode653.Valid := ⟨s1CachedNode649_valid,s1CachedNode652_valid⟩

def s1CachedNode654 : CachedPolynomialExpr 9 := .add s1CachedNode390 s1CachedNode339

theorem s1CachedNode654_valid : s1CachedNode654.Valid := ⟨s1CachedNode390_valid,s1CachedNode339_valid⟩

def s1CachedNode655 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode524

theorem s1CachedNode655_valid : s1CachedNode655.Valid := ⟨s1CachedNode20_valid,s1CachedNode524_valid⟩

def s1CachedNode656 : CachedPolynomialExpr 9 := .add s1CachedNode340 s1CachedNode655

theorem s1CachedNode656_valid : s1CachedNode656.Valid := ⟨s1CachedNode340_valid,s1CachedNode655_valid⟩

def s1CachedNode657 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode656

theorem s1CachedNode657_valid : s1CachedNode657.Valid := ⟨s1CachedNode178_valid,s1CachedNode656_valid⟩

def s1CachedNode658 : CachedPolynomialExpr 9 := .add s1CachedNode654 s1CachedNode657

theorem s1CachedNode658_valid : s1CachedNode658.Valid := ⟨s1CachedNode654_valid,s1CachedNode657_valid⟩

def s1CachedNode659 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode658

theorem s1CachedNode659_valid : s1CachedNode659.Valid := ⟨s1CachedNode178_valid,s1CachedNode658_valid⟩

def s1CachedNode660 : CachedPolynomialExpr 9 := .add s1CachedNode653 s1CachedNode659

theorem s1CachedNode660_valid : s1CachedNode660.Valid := ⟨s1CachedNode653_valid,s1CachedNode659_valid⟩

def s1CachedNode661 : CachedPolynomialExpr 9 := .mul s1CachedNode612 s1CachedNode4

theorem s1CachedNode661_valid : s1CachedNode661.Valid := ⟨s1CachedNode612_valid,s1CachedNode4_valid⟩

def s1CachedNode662 : CachedPolynomialExpr 9 := .add s1CachedNode610 s1CachedNode661

theorem s1CachedNode662_valid : s1CachedNode662.Valid := ⟨s1CachedNode610_valid,s1CachedNode661_valid⟩

def s1CachedNode663 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode662

theorem s1CachedNode663_valid : s1CachedNode663.Valid := ⟨s1CachedNode81_valid,s1CachedNode662_valid⟩

def s1CachedNode664 : CachedPolynomialExpr 9 := .add s1CachedNode660 s1CachedNode663

theorem s1CachedNode664_valid : s1CachedNode664.Valid := ⟨s1CachedNode660_valid,s1CachedNode663_valid⟩

def s1CachedNode665 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode664

theorem s1CachedNode665_valid : s1CachedNode665.Valid := ⟨s1CachedNode4_valid,s1CachedNode664_valid⟩

def s1CachedNode666 : CachedPolynomialExpr 9 := .add s1CachedNode647 s1CachedNode665

theorem s1CachedNode666_valid : s1CachedNode666.Valid := ⟨s1CachedNode647_valid,s1CachedNode665_valid⟩

def s1CachedNode667 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode390

theorem s1CachedNode667_valid : s1CachedNode667.Valid := ⟨s1CachedNode260_valid,s1CachedNode390_valid⟩

def s1CachedNode668 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode667

theorem s1CachedNode668_valid : s1CachedNode668.Valid := ⟨s1CachedNode178_valid,s1CachedNode667_valid⟩

def s1CachedNode669 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode668

theorem s1CachedNode669_valid : s1CachedNode669.Valid := ⟨s1CachedNode260_valid,s1CachedNode668_valid⟩

def s1CachedNode670 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode669

theorem s1CachedNode670_valid : s1CachedNode670.Valid := ⟨s1CachedNode178_valid,s1CachedNode669_valid⟩

def s1CachedNode671 : CachedPolynomialExpr 9 := .add s1CachedNode666 s1CachedNode670

theorem s1CachedNode671_valid : s1CachedNode671.Valid := ⟨s1CachedNode666_valid,s1CachedNode670_valid⟩

def s1CachedNode672 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode671

theorem s1CachedNode672_valid : s1CachedNode672.Valid := ⟨s1CachedNode1_valid,s1CachedNode671_valid⟩

def s1CachedHessian00 : CachedPolynomialExpr 9 := s1CachedNode672

theorem s1CachedHessian00_valid : s1CachedHessian00.Valid := s1CachedNode672_valid

theorem s1CachedHessian00_erase : s1CachedHessian00.erase = s1HornerHessian00 := by decide +kernel

def s1CachedNode673 : CachedPolynomialExpr 9 := .mul s1CachedNode136 s1CachedNode27

theorem s1CachedNode673_valid : s1CachedNode673.Valid := ⟨s1CachedNode136_valid,s1CachedNode27_valid⟩

def s1CachedNode674 : CachedPolynomialExpr 9 := .add s1CachedNode136 s1CachedNode673

theorem s1CachedNode674_valid : s1CachedNode674.Valid := ⟨s1CachedNode136_valid,s1CachedNode673_valid⟩

def s1CachedNode675 : CachedPolynomialExpr 9 := .mul s1CachedNode224 s1CachedNode4

theorem s1CachedNode675_valid : s1CachedNode675.Valid := ⟨s1CachedNode224_valid,s1CachedNode4_valid⟩

def s1CachedNode676 : CachedPolynomialExpr 9 := .mul s1CachedNode675 s1CachedNode47

theorem s1CachedNode676_valid : s1CachedNode676.Valid := ⟨s1CachedNode675_valid,s1CachedNode47_valid⟩

def s1CachedNode677 : CachedPolynomialExpr 9 := .add s1CachedNode674 s1CachedNode676

theorem s1CachedNode677_valid : s1CachedNode677.Valid := ⟨s1CachedNode674_valid,s1CachedNode676_valid⟩

def s1CachedNode678 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode677

theorem s1CachedNode678_valid : s1CachedNode678.Valid := ⟨s1CachedNode2_valid,s1CachedNode677_valid⟩

def s1CachedNode679 : CachedPolynomialExpr 9 := .rational (-6881924343606227/6755399441055744 : ℚ) ⟨-1174515087975462742,-1174515087975462741⟩

theorem s1CachedNode679_valid : s1CachedNode679.Valid := by decide +kernel

def s1CachedNode680 : CachedPolynomialExpr 9 := .mul s1CachedNode679 s1CachedNode27

theorem s1CachedNode680_valid : s1CachedNode680.Valid := ⟨s1CachedNode679_valid,s1CachedNode27_valid⟩

def s1CachedNode681 : CachedPolynomialExpr 9 := .add s1CachedNode679 s1CachedNode680

theorem s1CachedNode681_valid : s1CachedNode681.Valid := ⟨s1CachedNode679_valid,s1CachedNode680_valid⟩

def s1CachedNode682 : CachedPolynomialExpr 9 := .mul s1CachedNode13 s1CachedNode681

theorem s1CachedNode682_valid : s1CachedNode682.Valid := ⟨s1CachedNode13_valid,s1CachedNode681_valid⟩

def s1CachedNode683 : CachedPolynomialExpr 9 := .add s1CachedNode678 s1CachedNode682

theorem s1CachedNode683_valid : s1CachedNode683.Valid := ⟨s1CachedNode678_valid,s1CachedNode682_valid⟩

def s1CachedNode684 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode683

theorem s1CachedNode684_valid : s1CachedNode684.Valid := ⟨s1CachedNode1_valid,s1CachedNode683_valid⟩

def s1CachedNode685 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode2

theorem s1CachedNode685_valid : s1CachedNode685.Valid := ⟨s1CachedNode220_valid,s1CachedNode2_valid⟩

def s1CachedNode686 : CachedPolynomialExpr 9 := .mul s1CachedNode685 s1CachedNode4

theorem s1CachedNode686_valid : s1CachedNode686.Valid := ⟨s1CachedNode685_valid,s1CachedNode4_valid⟩

def s1CachedNode687 : CachedPolynomialExpr 9 := .mul s1CachedNode686 s1CachedNode47

theorem s1CachedNode687_valid : s1CachedNode687.Valid := ⟨s1CachedNode686_valid,s1CachedNode47_valid⟩

def s1CachedNode688 : CachedPolynomialExpr 9 := .add s1CachedNode684 s1CachedNode687

theorem s1CachedNode688_valid : s1CachedNode688.Valid := ⟨s1CachedNode684_valid,s1CachedNode687_valid⟩

def s1CachedNode689 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode688

theorem s1CachedNode689_valid : s1CachedNode689.Valid := ⟨s1CachedNode1_valid,s1CachedNode688_valid⟩

def s1CachedNode690 : CachedPolynomialExpr 9 := .rational (28189989383949979/27021597764222976 : ℚ) ⟨1202772880381865770,1202772880381865771⟩

theorem s1CachedNode690_valid : s1CachedNode690.Valid := by decide +kernel

def s1CachedNode691 : CachedPolynomialExpr 9 := .rational (-2521529215217977/54043195528445952 : ℚ) ⟨-53792623257983510,-53792623257983509⟩

theorem s1CachedNode691_valid : s1CachedNode691.Valid := by decide +kernel

def s1CachedNode692 : CachedPolynomialExpr 9 := .mul s1CachedNode691 s1CachedNode27

theorem s1CachedNode692_valid : s1CachedNode692.Valid := ⟨s1CachedNode691_valid,s1CachedNode27_valid⟩

def s1CachedNode693 : CachedPolynomialExpr 9 := .add s1CachedNode690 s1CachedNode692

theorem s1CachedNode693_valid : s1CachedNode693.Valid := ⟨s1CachedNode690_valid,s1CachedNode692_valid⟩

def s1CachedNode694 : CachedPolynomialExpr 9 := .add s1CachedNode693 s1CachedNode598

theorem s1CachedNode694_valid : s1CachedNode694.Valid := ⟨s1CachedNode693_valid,s1CachedNode598_valid⟩

def s1CachedNode695 : CachedPolynomialExpr 9 := .add s1CachedNode691 s1CachedNode605

theorem s1CachedNode695_valid : s1CachedNode695.Valid := ⟨s1CachedNode691_valid,s1CachedNode605_valid⟩

def s1CachedNode696 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode695

theorem s1CachedNode696_valid : s1CachedNode696.Valid := ⟨s1CachedNode20_valid,s1CachedNode695_valid⟩

def s1CachedNode697 : CachedPolynomialExpr 9 := .add s1CachedNode694 s1CachedNode696

theorem s1CachedNode697_valid : s1CachedNode697.Valid := ⟨s1CachedNode694_valid,s1CachedNode696_valid⟩

def s1CachedNode698 : CachedPolynomialExpr 9 := .mul s1CachedNode136 s1CachedNode20

theorem s1CachedNode698_valid : s1CachedNode698.Valid := ⟨s1CachedNode136_valid,s1CachedNode20_valid⟩

def s1CachedNode699 : CachedPolynomialExpr 9 := .add s1CachedNode136 s1CachedNode698

theorem s1CachedNode699_valid : s1CachedNode699.Valid := ⟨s1CachedNode136_valid,s1CachedNode698_valid⟩

def s1CachedNode700 : CachedPolynomialExpr 9 := .mul s1CachedNode679 s1CachedNode20

theorem s1CachedNode700_valid : s1CachedNode700.Valid := ⟨s1CachedNode679_valid,s1CachedNode20_valid⟩

def s1CachedNode701 : CachedPolynomialExpr 9 := .add s1CachedNode679 s1CachedNode700

theorem s1CachedNode701_valid : s1CachedNode701.Valid := ⟨s1CachedNode679_valid,s1CachedNode700_valid⟩

def s1CachedNode702 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode701

theorem s1CachedNode702_valid : s1CachedNode702.Valid := ⟨s1CachedNode2_valid,s1CachedNode701_valid⟩

def s1CachedNode703 : CachedPolynomialExpr 9 := .add s1CachedNode699 s1CachedNode702

theorem s1CachedNode703_valid : s1CachedNode703.Valid := ⟨s1CachedNode699_valid,s1CachedNode702_valid⟩

def s1CachedNode704 : CachedPolynomialExpr 9 := .add s1CachedNode703 s1CachedNode676

theorem s1CachedNode704_valid : s1CachedNode704.Valid := ⟨s1CachedNode703_valid,s1CachedNode676_valid⟩

def s1CachedNode705 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode704

theorem s1CachedNode705_valid : s1CachedNode705.Valid := ⟨s1CachedNode2_valid,s1CachedNode704_valid⟩

def s1CachedNode706 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode4

theorem s1CachedNode706_valid : s1CachedNode706.Valid := ⟨s1CachedNode220_valid,s1CachedNode4_valid⟩

def s1CachedNode707 : CachedPolynomialExpr 9 := .mul s1CachedNode706 s1CachedNode47

theorem s1CachedNode707_valid : s1CachedNode707.Valid := ⟨s1CachedNode706_valid,s1CachedNode47_valid⟩

def s1CachedNode708 : CachedPolynomialExpr 9 := .add s1CachedNode705 s1CachedNode707

theorem s1CachedNode708_valid : s1CachedNode708.Valid := ⟨s1CachedNode705_valid,s1CachedNode707_valid⟩

def s1CachedNode709 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode708

theorem s1CachedNode709_valid : s1CachedNode709.Valid := ⟨s1CachedNode2_valid,s1CachedNode708_valid⟩

def s1CachedNode710 : CachedPolynomialExpr 9 := .add s1CachedNode697 s1CachedNode709

theorem s1CachedNode710_valid : s1CachedNode710.Valid := ⟨s1CachedNode697_valid,s1CachedNode709_valid⟩

def s1CachedNode711 : CachedPolynomialExpr 9 := .add s1CachedNode710 s1CachedNode637

theorem s1CachedNode711_valid : s1CachedNode711.Valid := ⟨s1CachedNode710_valid,s1CachedNode637_valid⟩

def s1CachedNode712 : CachedPolynomialExpr 9 := .mul s1CachedNode261 s1CachedNode27

theorem s1CachedNode712_valid : s1CachedNode712.Valid := ⟨s1CachedNode261_valid,s1CachedNode27_valid⟩

def s1CachedNode713 : CachedPolynomialExpr 9 := .mul s1CachedNode712 s1CachedNode178

theorem s1CachedNode713_valid : s1CachedNode713.Valid := ⟨s1CachedNode712_valid,s1CachedNode178_valid⟩

def s1CachedNode714 : CachedPolynomialExpr 9 := .add s1CachedNode639 s1CachedNode713

theorem s1CachedNode714_valid : s1CachedNode714.Valid := ⟨s1CachedNode639_valid,s1CachedNode713_valid⟩

def s1CachedNode715 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode714

theorem s1CachedNode715_valid : s1CachedNode715.Valid := ⟨s1CachedNode178_valid,s1CachedNode714_valid⟩

def s1CachedNode716 : CachedPolynomialExpr 9 := .add s1CachedNode711 s1CachedNode715

theorem s1CachedNode716_valid : s1CachedNode716.Valid := ⟨s1CachedNode711_valid,s1CachedNode715_valid⟩

def s1CachedNode717 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode716

theorem s1CachedNode717_valid : s1CachedNode717.Valid := ⟨s1CachedNode2_valid,s1CachedNode716_valid⟩

def s1CachedNode718 : CachedPolynomialExpr 9 := .add s1CachedNode689 s1CachedNode717

theorem s1CachedNode718_valid : s1CachedNode718.Valid := ⟨s1CachedNode689_valid,s1CachedNode717_valid⟩

def s1CachedNode719 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode718

theorem s1CachedNode719_valid : s1CachedNode719.Valid := ⟨s1CachedNode1_valid,s1CachedNode718_valid⟩

def s1CachedHessian01 : CachedPolynomialExpr 9 := s1CachedNode719

theorem s1CachedHessian01_valid : s1CachedHessian01.Valid := s1CachedNode719_valid

theorem s1CachedHessian01_erase : s1CachedHessian01.erase = s1HornerHessian01 := by decide +kernel

def s1CachedNode720 : CachedPolynomialExpr 9 := .mul s1CachedNode136 s1CachedNode34

theorem s1CachedNode720_valid : s1CachedNode720.Valid := ⟨s1CachedNode136_valid,s1CachedNode34_valid⟩

def s1CachedNode721 : CachedPolynomialExpr 9 := .add s1CachedNode136 s1CachedNode720

theorem s1CachedNode721_valid : s1CachedNode721.Valid := ⟨s1CachedNode136_valid,s1CachedNode720_valid⟩

def s1CachedNode722 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode721

theorem s1CachedNode722_valid : s1CachedNode722.Valid := ⟨s1CachedNode4_valid,s1CachedNode721_valid⟩

def s1CachedNode723 : CachedPolynomialExpr 9 := .mul s1CachedNode679 s1CachedNode34

theorem s1CachedNode723_valid : s1CachedNode723.Valid := ⟨s1CachedNode679_valid,s1CachedNode34_valid⟩

def s1CachedNode724 : CachedPolynomialExpr 9 := .add s1CachedNode679 s1CachedNode723

theorem s1CachedNode724_valid : s1CachedNode724.Valid := ⟨s1CachedNode679_valid,s1CachedNode723_valid⟩

def s1CachedNode725 : CachedPolynomialExpr 9 := .mul s1CachedNode447 s1CachedNode724

theorem s1CachedNode725_valid : s1CachedNode725.Valid := ⟨s1CachedNode447_valid,s1CachedNode724_valid⟩

def s1CachedNode726 : CachedPolynomialExpr 9 := .add s1CachedNode722 s1CachedNode725

theorem s1CachedNode726_valid : s1CachedNode726.Valid := ⟨s1CachedNode722_valid,s1CachedNode725_valid⟩

def s1CachedNode727 : CachedPolynomialExpr 9 := .mul s1CachedNode224 s1CachedNode2

theorem s1CachedNode727_valid : s1CachedNode727.Valid := ⟨s1CachedNode224_valid,s1CachedNode2_valid⟩

def s1CachedNode728 : CachedPolynomialExpr 9 := .mul s1CachedNode727 s1CachedNode4

theorem s1CachedNode728_valid : s1CachedNode728.Valid := ⟨s1CachedNode727_valid,s1CachedNode4_valid⟩

def s1CachedNode729 : CachedPolynomialExpr 9 := .mul s1CachedNode728 s1CachedNode47

theorem s1CachedNode729_valid : s1CachedNode729.Valid := ⟨s1CachedNode728_valid,s1CachedNode47_valid⟩

def s1CachedNode730 : CachedPolynomialExpr 9 := .add s1CachedNode726 s1CachedNode729

theorem s1CachedNode730_valid : s1CachedNode730.Valid := ⟨s1CachedNode726_valid,s1CachedNode729_valid⟩

def s1CachedNode731 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode730

theorem s1CachedNode731_valid : s1CachedNode731.Valid := ⟨s1CachedNode1_valid,s1CachedNode730_valid⟩

def s1CachedNode732 : CachedPolynomialExpr 9 := .add s1CachedNode731 s1CachedNode687

theorem s1CachedNode732_valid : s1CachedNode732.Valid := ⟨s1CachedNode731_valid,s1CachedNode687_valid⟩

def s1CachedNode733 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode732

theorem s1CachedNode733_valid : s1CachedNode733.Valid := ⟨s1CachedNode1_valid,s1CachedNode732_valid⟩

def s1CachedNode734 : CachedPolynomialExpr 9 := .mul s1CachedNode615 s1CachedNode2

theorem s1CachedNode734_valid : s1CachedNode734.Valid := ⟨s1CachedNode615_valid,s1CachedNode2_valid⟩

def s1CachedNode735 : CachedPolynomialExpr 9 := .mul s1CachedNode734 s1CachedNode4

theorem s1CachedNode735_valid : s1CachedNode735.Valid := ⟨s1CachedNode734_valid,s1CachedNode4_valid⟩

def s1CachedNode736 : CachedPolynomialExpr 9 := .mul s1CachedNode735 s1CachedNode47

theorem s1CachedNode736_valid : s1CachedNode736.Valid := ⟨s1CachedNode735_valid,s1CachedNode47_valid⟩

def s1CachedNode737 : CachedPolynomialExpr 9 := .add s1CachedNode622 s1CachedNode736

theorem s1CachedNode737_valid : s1CachedNode737.Valid := ⟨s1CachedNode622_valid,s1CachedNode736_valid⟩

def s1CachedNode738 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode737

theorem s1CachedNode738_valid : s1CachedNode738.Valid := ⟨s1CachedNode2_valid,s1CachedNode737_valid⟩

def s1CachedNode739 : CachedPolynomialExpr 9 := .mul s1CachedNode220 s1CachedNode47

theorem s1CachedNode739_valid : s1CachedNode739.Valid := ⟨s1CachedNode220_valid,s1CachedNode47_valid⟩

def s1CachedNode740 : CachedPolynomialExpr 9 := .add s1CachedNode739 s1CachedNode676

theorem s1CachedNode740_valid : s1CachedNode740.Valid := ⟨s1CachedNode739_valid,s1CachedNode676_valid⟩

def s1CachedNode741 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode740

theorem s1CachedNode741_valid : s1CachedNode741.Valid := ⟨s1CachedNode4_valid,s1CachedNode740_valid⟩

def s1CachedNode742 : CachedPolynomialExpr 9 := .add s1CachedNode626 s1CachedNode741

theorem s1CachedNode742_valid : s1CachedNode742.Valid := ⟨s1CachedNode626_valid,s1CachedNode741_valid⟩

def s1CachedNode743 : CachedPolynomialExpr 9 := .add s1CachedNode742 s1CachedNode635

theorem s1CachedNode743_valid : s1CachedNode743.Valid := ⟨s1CachedNode742_valid,s1CachedNode635_valid⟩

def s1CachedNode744 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode743

theorem s1CachedNode744_valid : s1CachedNode744.Valid := ⟨s1CachedNode4_valid,s1CachedNode743_valid⟩

def s1CachedNode745 : CachedPolynomialExpr 9 := .add s1CachedNode738 s1CachedNode744

theorem s1CachedNode745_valid : s1CachedNode745.Valid := ⟨s1CachedNode738_valid,s1CachedNode744_valid⟩

def s1CachedNode746 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode745

theorem s1CachedNode746_valid : s1CachedNode746.Valid := ⟨s1CachedNode2_valid,s1CachedNode745_valid⟩

def s1CachedNode747 : CachedPolynomialExpr 9 := .add s1CachedNode733 s1CachedNode746

theorem s1CachedNode747_valid : s1CachedNode747.Valid := ⟨s1CachedNode733_valid,s1CachedNode746_valid⟩

def s1CachedNode748 : CachedPolynomialExpr 9 := .mul s1CachedNode691 s1CachedNode34

theorem s1CachedNode748_valid : s1CachedNode748.Valid := ⟨s1CachedNode691_valid,s1CachedNode34_valid⟩

def s1CachedNode749 : CachedPolynomialExpr 9 := .add s1CachedNode690 s1CachedNode748

theorem s1CachedNode749_valid : s1CachedNode749.Valid := ⟨s1CachedNode690_valid,s1CachedNode748_valid⟩

def s1CachedNode750 : CachedPolynomialExpr 9 := .add s1CachedNode749 s1CachedNode598

theorem s1CachedNode750_valid : s1CachedNode750.Valid := ⟨s1CachedNode749_valid,s1CachedNode598_valid⟩

def s1CachedNode751 : CachedPolynomialExpr 9 := .add s1CachedNode691 s1CachedNode650

theorem s1CachedNode751_valid : s1CachedNode751.Valid := ⟨s1CachedNode691_valid,s1CachedNode650_valid⟩

def s1CachedNode752 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode751

theorem s1CachedNode752_valid : s1CachedNode752.Valid := ⟨s1CachedNode20_valid,s1CachedNode751_valid⟩

def s1CachedNode753 : CachedPolynomialExpr 9 := .add s1CachedNode750 s1CachedNode752

theorem s1CachedNode753_valid : s1CachedNode753.Valid := ⟨s1CachedNode750_valid,s1CachedNode752_valid⟩

def s1CachedNode754 : CachedPolynomialExpr 9 := .mul s1CachedNode261 s1CachedNode34

theorem s1CachedNode754_valid : s1CachedNode754.Valid := ⟨s1CachedNode261_valid,s1CachedNode34_valid⟩

def s1CachedNode755 : CachedPolynomialExpr 9 := .mul s1CachedNode754 s1CachedNode178

theorem s1CachedNode755_valid : s1CachedNode755.Valid := ⟨s1CachedNode754_valid,s1CachedNode178_valid⟩

def s1CachedNode756 : CachedPolynomialExpr 9 := .add s1CachedNode654 s1CachedNode755

theorem s1CachedNode756_valid : s1CachedNode756.Valid := ⟨s1CachedNode654_valid,s1CachedNode755_valid⟩

def s1CachedNode757 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode756

theorem s1CachedNode757_valid : s1CachedNode757.Valid := ⟨s1CachedNode178_valid,s1CachedNode756_valid⟩

def s1CachedNode758 : CachedPolynomialExpr 9 := .add s1CachedNode753 s1CachedNode757

theorem s1CachedNode758_valid : s1CachedNode758.Valid := ⟨s1CachedNode753_valid,s1CachedNode757_valid⟩

def s1CachedNode759 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode701

theorem s1CachedNode759_valid : s1CachedNode759.Valid := ⟨s1CachedNode4_valid,s1CachedNode701_valid⟩

def s1CachedNode760 : CachedPolynomialExpr 9 := .add s1CachedNode699 s1CachedNode759

theorem s1CachedNode760_valid : s1CachedNode760.Valid := ⟨s1CachedNode699_valid,s1CachedNode759_valid⟩

def s1CachedNode761 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode760

theorem s1CachedNode761_valid : s1CachedNode761.Valid := ⟨s1CachedNode81_valid,s1CachedNode760_valid⟩

def s1CachedNode762 : CachedPolynomialExpr 9 := .add s1CachedNode758 s1CachedNode761

theorem s1CachedNode762_valid : s1CachedNode762.Valid := ⟨s1CachedNode758_valid,s1CachedNode761_valid⟩

def s1CachedNode763 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode762

theorem s1CachedNode763_valid : s1CachedNode763.Valid := ⟨s1CachedNode4_valid,s1CachedNode762_valid⟩

def s1CachedNode764 : CachedPolynomialExpr 9 := .add s1CachedNode747 s1CachedNode763

theorem s1CachedNode764_valid : s1CachedNode764.Valid := ⟨s1CachedNode747_valid,s1CachedNode763_valid⟩

def s1CachedNode765 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode764

theorem s1CachedNode765_valid : s1CachedNode765.Valid := ⟨s1CachedNode1_valid,s1CachedNode764_valid⟩

def s1CachedHessian02 : CachedPolynomialExpr 9 := s1CachedNode765

theorem s1CachedHessian02_valid : s1CachedHessian02.Valid := s1CachedNode765_valid

theorem s1CachedHessian02_erase : s1CachedHessian02.erase = s1HornerHessian02 := by decide +kernel

def s1CachedHessian10 : CachedPolynomialExpr 9 := s1CachedNode719

theorem s1CachedHessian10_valid : s1CachedHessian10.Valid := s1CachedNode719_valid

theorem s1CachedHessian10_erase : s1CachedHessian10.erase = s1HornerHessian10 := by decide +kernel

def s1CachedNode766 : CachedPolynomialExpr 9 := .mul s1CachedNode609 s1CachedNode27

theorem s1CachedNode766_valid : s1CachedNode766.Valid := ⟨s1CachedNode609_valid,s1CachedNode27_valid⟩

def s1CachedNode767 : CachedPolynomialExpr 9 := .add s1CachedNode766 s1CachedNode617

theorem s1CachedNode767_valid : s1CachedNode767.Valid := ⟨s1CachedNode766_valid,s1CachedNode617_valid⟩

def s1CachedNode768 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode767

theorem s1CachedNode768_valid : s1CachedNode768.Valid := ⟨s1CachedNode2_valid,s1CachedNode767_valid⟩

def s1CachedNode769 : CachedPolynomialExpr 9 := .mul s1CachedNode611 s1CachedNode27

theorem s1CachedNode769_valid : s1CachedNode769.Valid := ⟨s1CachedNode611_valid,s1CachedNode27_valid⟩

def s1CachedNode770 : CachedPolynomialExpr 9 := .mul s1CachedNode769 s1CachedNode1

theorem s1CachedNode770_valid : s1CachedNode770.Valid := ⟨s1CachedNode769_valid,s1CachedNode1_valid⟩

def s1CachedNode771 : CachedPolynomialExpr 9 := .mul s1CachedNode770 s1CachedNode2

theorem s1CachedNode771_valid : s1CachedNode771.Valid := ⟨s1CachedNode770_valid,s1CachedNode2_valid⟩

def s1CachedNode772 : CachedPolynomialExpr 9 := .add s1CachedNode768 s1CachedNode771

theorem s1CachedNode772_valid : s1CachedNode772.Valid := ⟨s1CachedNode768_valid,s1CachedNode771_valid⟩

def s1CachedNode773 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode772

theorem s1CachedNode773_valid : s1CachedNode773.Valid := ⟨s1CachedNode1_valid,s1CachedNode772_valid⟩

def s1CachedNode774 : CachedPolynomialExpr 9 := .mul s1CachedNode620 s1CachedNode2

theorem s1CachedNode774_valid : s1CachedNode774.Valid := ⟨s1CachedNode620_valid,s1CachedNode2_valid⟩

def s1CachedNode775 : CachedPolynomialExpr 9 := .mul s1CachedNode774 s1CachedNode4

theorem s1CachedNode775_valid : s1CachedNode775.Valid := ⟨s1CachedNode774_valid,s1CachedNode4_valid⟩

def s1CachedNode776 : CachedPolynomialExpr 9 := .mul s1CachedNode775 s1CachedNode47

theorem s1CachedNode776_valid : s1CachedNode776.Valid := ⟨s1CachedNode775_valid,s1CachedNode47_valid⟩

def s1CachedNode777 : CachedPolynomialExpr 9 := .add s1CachedNode773 s1CachedNode776

theorem s1CachedNode777_valid : s1CachedNode777.Valid := ⟨s1CachedNode773_valid,s1CachedNode776_valid⟩

def s1CachedNode778 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode777

theorem s1CachedNode778_valid : s1CachedNode778.Valid := ⟨s1CachedNode1_valid,s1CachedNode777_valid⟩

def s1CachedNode779 : CachedPolynomialExpr 9 := .mul s1CachedNode603 s1CachedNode27

theorem s1CachedNode779_valid : s1CachedNode779.Valid := ⟨s1CachedNode603_valid,s1CachedNode27_valid⟩

def s1CachedNode780 : CachedPolynomialExpr 9 := .add s1CachedNode596 s1CachedNode779

theorem s1CachedNode780_valid : s1CachedNode780.Valid := ⟨s1CachedNode596_valid,s1CachedNode779_valid⟩

def s1CachedNode781 : CachedPolynomialExpr 9 := .add s1CachedNode780 s1CachedNode598

theorem s1CachedNode781_valid : s1CachedNode781.Valid := ⟨s1CachedNode780_valid,s1CachedNode598_valid⟩

def s1CachedNode782 : CachedPolynomialExpr 9 := .add s1CachedNode600 s1CachedNode605

theorem s1CachedNode782_valid : s1CachedNode782.Valid := ⟨s1CachedNode600_valid,s1CachedNode605_valid⟩

def s1CachedNode783 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode782

theorem s1CachedNode783_valid : s1CachedNode783.Valid := ⟨s1CachedNode20_valid,s1CachedNode782_valid⟩

def s1CachedNode784 : CachedPolynomialExpr 9 := .add s1CachedNode781 s1CachedNode783

theorem s1CachedNode784_valid : s1CachedNode784.Valid := ⟨s1CachedNode781_valid,s1CachedNode783_valid⟩

def s1CachedNode785 : CachedPolynomialExpr 9 := .mul s1CachedNode564 s1CachedNode20

theorem s1CachedNode785_valid : s1CachedNode785.Valid := ⟨s1CachedNode564_valid,s1CachedNode20_valid⟩

def s1CachedNode786 : CachedPolynomialExpr 9 := .add s1CachedNode563 s1CachedNode785

theorem s1CachedNode786_valid : s1CachedNode786.Valid := ⟨s1CachedNode563_valid,s1CachedNode785_valid⟩

def s1CachedNode787 : CachedPolynomialExpr 9 := .mul s1CachedNode552 s1CachedNode20

theorem s1CachedNode787_valid : s1CachedNode787.Valid := ⟨s1CachedNode552_valid,s1CachedNode20_valid⟩

def s1CachedNode788 : CachedPolynomialExpr 9 := .add s1CachedNode551 s1CachedNode787

theorem s1CachedNode788_valid : s1CachedNode788.Valid := ⟨s1CachedNode551_valid,s1CachedNode787_valid⟩

def s1CachedNode789 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode788

theorem s1CachedNode789_valid : s1CachedNode789.Valid := ⟨s1CachedNode2_valid,s1CachedNode788_valid⟩

def s1CachedNode790 : CachedPolynomialExpr 9 := .add s1CachedNode786 s1CachedNode789

theorem s1CachedNode790_valid : s1CachedNode790.Valid := ⟨s1CachedNode786_valid,s1CachedNode789_valid⟩

def s1CachedNode791 : CachedPolynomialExpr 9 := .add s1CachedNode790 s1CachedNode569

theorem s1CachedNode791_valid : s1CachedNode791.Valid := ⟨s1CachedNode790_valid,s1CachedNode569_valid⟩

def s1CachedNode792 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode791

theorem s1CachedNode792_valid : s1CachedNode792.Valid := ⟨s1CachedNode2_valid,s1CachedNode791_valid⟩

def s1CachedNode793 : CachedPolynomialExpr 9 := .mul s1CachedNode589 s1CachedNode4

theorem s1CachedNode793_valid : s1CachedNode793.Valid := ⟨s1CachedNode589_valid,s1CachedNode4_valid⟩

def s1CachedNode794 : CachedPolynomialExpr 9 := .mul s1CachedNode793 s1CachedNode47

theorem s1CachedNode794_valid : s1CachedNode794.Valid := ⟨s1CachedNode793_valid,s1CachedNode47_valid⟩

def s1CachedNode795 : CachedPolynomialExpr 9 := .add s1CachedNode792 s1CachedNode794

theorem s1CachedNode795_valid : s1CachedNode795.Valid := ⟨s1CachedNode792_valid,s1CachedNode794_valid⟩

def s1CachedNode796 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode795

theorem s1CachedNode796_valid : s1CachedNode796.Valid := ⟨s1CachedNode2_valid,s1CachedNode795_valid⟩

def s1CachedNode797 : CachedPolynomialExpr 9 := .add s1CachedNode784 s1CachedNode796

theorem s1CachedNode797_valid : s1CachedNode797.Valid := ⟨s1CachedNode784_valid,s1CachedNode796_valid⟩

def s1CachedNode798 : CachedPolynomialExpr 9 := .add s1CachedNode797 s1CachedNode637

theorem s1CachedNode798_valid : s1CachedNode798.Valid := ⟨s1CachedNode797_valid,s1CachedNode637_valid⟩

def s1CachedNode799 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode321

theorem s1CachedNode799_valid : s1CachedNode799.Valid := ⟨s1CachedNode255_valid,s1CachedNode321_valid⟩

def s1CachedNode800 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode799

theorem s1CachedNode800_valid : s1CachedNode800.Valid := ⟨s1CachedNode20_valid,s1CachedNode799_valid⟩

def s1CachedNode801 : CachedPolynomialExpr 9 := .add s1CachedNode799 s1CachedNode800

theorem s1CachedNode801_valid : s1CachedNode801.Valid := ⟨s1CachedNode799_valid,s1CachedNode800_valid⟩

def s1CachedNode802 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode801

theorem s1CachedNode802_valid : s1CachedNode802.Valid := ⟨s1CachedNode178_valid,s1CachedNode801_valid⟩

def s1CachedNode803 : CachedPolynomialExpr 9 := .add s1CachedNode639 s1CachedNode802

theorem s1CachedNode803_valid : s1CachedNode803.Valid := ⟨s1CachedNode639_valid,s1CachedNode802_valid⟩

def s1CachedNode804 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode803

theorem s1CachedNode804_valid : s1CachedNode804.Valid := ⟨s1CachedNode178_valid,s1CachedNode803_valid⟩

def s1CachedNode805 : CachedPolynomialExpr 9 := .add s1CachedNode798 s1CachedNode804

theorem s1CachedNode805_valid : s1CachedNode805.Valid := ⟨s1CachedNode798_valid,s1CachedNode804_valid⟩

def s1CachedNode806 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode805

theorem s1CachedNode806_valid : s1CachedNode806.Valid := ⟨s1CachedNode2_valid,s1CachedNode805_valid⟩

def s1CachedNode807 : CachedPolynomialExpr 9 := .add s1CachedNode778 s1CachedNode806

theorem s1CachedNode807_valid : s1CachedNode807.Valid := ⟨s1CachedNode778_valid,s1CachedNode806_valid⟩

def s1CachedNode808 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode807

theorem s1CachedNode808_valid : s1CachedNode808.Valid := ⟨s1CachedNode1_valid,s1CachedNode807_valid⟩

def s1CachedNode809 : CachedPolynomialExpr 9 := .add s1CachedNode538 s1CachedNode313

theorem s1CachedNode809_valid : s1CachedNode809.Valid := ⟨s1CachedNode538_valid,s1CachedNode313_valid⟩

def s1CachedNode810 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode809

theorem s1CachedNode810_valid : s1CachedNode810.Valid := ⟨s1CachedNode27_valid,s1CachedNode809_valid⟩

def s1CachedNode811 : CachedPolynomialExpr 9 := .add s1CachedNode537 s1CachedNode810

theorem s1CachedNode811_valid : s1CachedNode811.Valid := ⟨s1CachedNode537_valid,s1CachedNode810_valid⟩

def s1CachedNode812 : CachedPolynomialExpr 9 := .mul s1CachedNode543 s1CachedNode27

theorem s1CachedNode812_valid : s1CachedNode812.Valid := ⟨s1CachedNode543_valid,s1CachedNode27_valid⟩

def s1CachedNode813 : CachedPolynomialExpr 9 := .add s1CachedNode542 s1CachedNode812

theorem s1CachedNode813_valid : s1CachedNode813.Valid := ⟨s1CachedNode542_valid,s1CachedNode812_valid⟩

def s1CachedNode814 : CachedPolynomialExpr 9 := .mul s1CachedNode547 s1CachedNode27

theorem s1CachedNode814_valid : s1CachedNode814.Valid := ⟨s1CachedNode547_valid,s1CachedNode27_valid⟩

def s1CachedNode815 : CachedPolynomialExpr 9 := .add s1CachedNode546 s1CachedNode814

theorem s1CachedNode815_valid : s1CachedNode815.Valid := ⟨s1CachedNode546_valid,s1CachedNode814_valid⟩

def s1CachedNode816 : CachedPolynomialExpr 9 := .add s1CachedNode550 s1CachedNode559

theorem s1CachedNode816_valid : s1CachedNode816.Valid := ⟨s1CachedNode550_valid,s1CachedNode559_valid⟩

def s1CachedNode817 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode816

theorem s1CachedNode817_valid : s1CachedNode817.Valid := ⟨s1CachedNode2_valid,s1CachedNode816_valid⟩

def s1CachedNode818 : CachedPolynomialExpr 9 := .add s1CachedNode815 s1CachedNode817

theorem s1CachedNode818_valid : s1CachedNode818.Valid := ⟨s1CachedNode815_valid,s1CachedNode817_valid⟩

def s1CachedNode819 : CachedPolynomialExpr 9 := .add s1CachedNode818 s1CachedNode575

theorem s1CachedNode819_valid : s1CachedNode819.Valid := ⟨s1CachedNode818_valid,s1CachedNode575_valid⟩

def s1CachedNode820 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode819

theorem s1CachedNode820_valid : s1CachedNode820.Valid := ⟨s1CachedNode2_valid,s1CachedNode819_valid⟩

def s1CachedNode821 : CachedPolynomialExpr 9 := .add s1CachedNode813 s1CachedNode820

theorem s1CachedNode821_valid : s1CachedNode821.Valid := ⟨s1CachedNode813_valid,s1CachedNode820_valid⟩

def s1CachedNode822 : CachedPolynomialExpr 9 := .mul s1CachedNode579 s1CachedNode27

theorem s1CachedNode822_valid : s1CachedNode822.Valid := ⟨s1CachedNode579_valid,s1CachedNode27_valid⟩

def s1CachedNode823 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode27

theorem s1CachedNode823_valid : s1CachedNode823.Valid := ⟨s1CachedNode25_valid,s1CachedNode27_valid⟩

def s1CachedNode824 : CachedPolynomialExpr 9 := .mul s1CachedNode823 s1CachedNode27

theorem s1CachedNode824_valid : s1CachedNode824.Valid := ⟨s1CachedNode823_valid,s1CachedNode27_valid⟩

def s1CachedNode825 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode824

theorem s1CachedNode825_valid : s1CachedNode825.Valid := ⟨s1CachedNode256_valid,s1CachedNode824_valid⟩

def s1CachedNode826 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode825

theorem s1CachedNode826_valid : s1CachedNode826.Valid := ⟨s1CachedNode260_valid,s1CachedNode825_valid⟩

def s1CachedNode827 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode826

theorem s1CachedNode827_valid : s1CachedNode827.Valid := ⟨s1CachedNode178_valid,s1CachedNode826_valid⟩

def s1CachedNode828 : CachedPolynomialExpr 9 := .add s1CachedNode822 s1CachedNode827

theorem s1CachedNode828_valid : s1CachedNode828.Valid := ⟨s1CachedNode822_valid,s1CachedNode827_valid⟩

def s1CachedNode829 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode828

theorem s1CachedNode829_valid : s1CachedNode829.Valid := ⟨s1CachedNode178_valid,s1CachedNode828_valid⟩

def s1CachedNode830 : CachedPolynomialExpr 9 := .add s1CachedNode821 s1CachedNode829

theorem s1CachedNode830_valid : s1CachedNode830.Valid := ⟨s1CachedNode821_valid,s1CachedNode829_valid⟩

def s1CachedNode831 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode830

theorem s1CachedNode831_valid : s1CachedNode831.Valid := ⟨s1CachedNode2_valid,s1CachedNode830_valid⟩

def s1CachedNode832 : CachedPolynomialExpr 9 := .add s1CachedNode811 s1CachedNode831

theorem s1CachedNode832_valid : s1CachedNode832.Valid := ⟨s1CachedNode811_valid,s1CachedNode831_valid⟩

def s1CachedNode833 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode651

theorem s1CachedNode833_valid : s1CachedNode833.Valid := ⟨s1CachedNode27_valid,s1CachedNode651_valid⟩

def s1CachedNode834 : CachedPolynomialExpr 9 := .add s1CachedNode649 s1CachedNode833

theorem s1CachedNode834_valid : s1CachedNode834.Valid := ⟨s1CachedNode649_valid,s1CachedNode833_valid⟩

def s1CachedNode835 : CachedPolynomialExpr 9 := .add s1CachedNode323 s1CachedNode339

theorem s1CachedNode835_valid : s1CachedNode835.Valid := ⟨s1CachedNode323_valid,s1CachedNode339_valid⟩

def s1CachedNode836 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode524

theorem s1CachedNode836_valid : s1CachedNode836.Valid := ⟨s1CachedNode27_valid,s1CachedNode524_valid⟩

def s1CachedNode837 : CachedPolynomialExpr 9 := .add s1CachedNode340 s1CachedNode836

theorem s1CachedNode837_valid : s1CachedNode837.Valid := ⟨s1CachedNode340_valid,s1CachedNode836_valid⟩

def s1CachedNode838 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode837

theorem s1CachedNode838_valid : s1CachedNode838.Valid := ⟨s1CachedNode178_valid,s1CachedNode837_valid⟩

def s1CachedNode839 : CachedPolynomialExpr 9 := .add s1CachedNode835 s1CachedNode838

theorem s1CachedNode839_valid : s1CachedNode839.Valid := ⟨s1CachedNode835_valid,s1CachedNode838_valid⟩

def s1CachedNode840 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode839

theorem s1CachedNode840_valid : s1CachedNode840.Valid := ⟨s1CachedNode178_valid,s1CachedNode839_valid⟩

def s1CachedNode841 : CachedPolynomialExpr 9 := .add s1CachedNode834 s1CachedNode840

theorem s1CachedNode841_valid : s1CachedNode841.Valid := ⟨s1CachedNode834_valid,s1CachedNode840_valid⟩

def s1CachedNode842 : CachedPolynomialExpr 9 := .mul s1CachedNode769 s1CachedNode4

theorem s1CachedNode842_valid : s1CachedNode842.Valid := ⟨s1CachedNode769_valid,s1CachedNode4_valid⟩

def s1CachedNode843 : CachedPolynomialExpr 9 := .add s1CachedNode766 s1CachedNode842

theorem s1CachedNode843_valid : s1CachedNode843.Valid := ⟨s1CachedNode766_valid,s1CachedNode842_valid⟩

def s1CachedNode844 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode843

theorem s1CachedNode844_valid : s1CachedNode844.Valid := ⟨s1CachedNode81_valid,s1CachedNode843_valid⟩

def s1CachedNode845 : CachedPolynomialExpr 9 := .add s1CachedNode841 s1CachedNode844

theorem s1CachedNode845_valid : s1CachedNode845.Valid := ⟨s1CachedNode841_valid,s1CachedNode844_valid⟩

def s1CachedNode846 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode845

theorem s1CachedNode846_valid : s1CachedNode846.Valid := ⟨s1CachedNode4_valid,s1CachedNode845_valid⟩

def s1CachedNode847 : CachedPolynomialExpr 9 := .add s1CachedNode832 s1CachedNode846

theorem s1CachedNode847_valid : s1CachedNode847.Valid := ⟨s1CachedNode832_valid,s1CachedNode846_valid⟩

def s1CachedNode848 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode323

theorem s1CachedNode848_valid : s1CachedNode848.Valid := ⟨s1CachedNode260_valid,s1CachedNode323_valid⟩

def s1CachedNode849 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode848

theorem s1CachedNode849_valid : s1CachedNode849.Valid := ⟨s1CachedNode178_valid,s1CachedNode848_valid⟩

def s1CachedNode850 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode849

theorem s1CachedNode850_valid : s1CachedNode850.Valid := ⟨s1CachedNode260_valid,s1CachedNode849_valid⟩

def s1CachedNode851 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode850

theorem s1CachedNode851_valid : s1CachedNode851.Valid := ⟨s1CachedNode178_valid,s1CachedNode850_valid⟩

def s1CachedNode852 : CachedPolynomialExpr 9 := .add s1CachedNode847 s1CachedNode851

theorem s1CachedNode852_valid : s1CachedNode852.Valid := ⟨s1CachedNode847_valid,s1CachedNode851_valid⟩

def s1CachedNode853 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode852

theorem s1CachedNode853_valid : s1CachedNode853.Valid := ⟨s1CachedNode2_valid,s1CachedNode852_valid⟩

def s1CachedNode854 : CachedPolynomialExpr 9 := .add s1CachedNode808 s1CachedNode853

theorem s1CachedNode854_valid : s1CachedNode854.Valid := ⟨s1CachedNode808_valid,s1CachedNode853_valid⟩

def s1CachedHessian11 : CachedPolynomialExpr 9 := s1CachedNode854

theorem s1CachedHessian11_valid : s1CachedHessian11.Valid := s1CachedNode854_valid

theorem s1CachedHessian11_erase : s1CachedHessian11.erase = s1HornerHessian11 := by decide +kernel

def s1CachedNode855 : CachedPolynomialExpr 9 := .mul s1CachedNode615 s1CachedNode1

theorem s1CachedNode855_valid : s1CachedNode855.Valid := ⟨s1CachedNode615_valid,s1CachedNode1_valid⟩

def s1CachedNode856 : CachedPolynomialExpr 9 := .mul s1CachedNode855 s1CachedNode2

theorem s1CachedNode856_valid : s1CachedNode856.Valid := ⟨s1CachedNode855_valid,s1CachedNode2_valid⟩

def s1CachedNode857 : CachedPolynomialExpr 9 := .mul s1CachedNode856 s1CachedNode4

theorem s1CachedNode857_valid : s1CachedNode857.Valid := ⟨s1CachedNode856_valid,s1CachedNode4_valid⟩

def s1CachedNode858 : CachedPolynomialExpr 9 := .mul s1CachedNode857 s1CachedNode47

theorem s1CachedNode858_valid : s1CachedNode858.Valid := ⟨s1CachedNode857_valid,s1CachedNode47_valid⟩

def s1CachedNode859 : CachedPolynomialExpr 9 := .add s1CachedNode776 s1CachedNode858

theorem s1CachedNode859_valid : s1CachedNode859.Valid := ⟨s1CachedNode776_valid,s1CachedNode858_valid⟩

def s1CachedNode860 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode859

theorem s1CachedNode860_valid : s1CachedNode860.Valid := ⟨s1CachedNode1_valid,s1CachedNode859_valid⟩

def s1CachedNode861 : CachedPolynomialExpr 9 := .add s1CachedNode707 s1CachedNode729

theorem s1CachedNode861_valid : s1CachedNode861.Valid := ⟨s1CachedNode707_valid,s1CachedNode729_valid⟩

def s1CachedNode862 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode861

theorem s1CachedNode862_valid : s1CachedNode862.Valid := ⟨s1CachedNode2_valid,s1CachedNode861_valid⟩

def s1CachedNode863 : CachedPolynomialExpr 9 := .add s1CachedNode862 s1CachedNode744

theorem s1CachedNode863_valid : s1CachedNode863.Valid := ⟨s1CachedNode862_valid,s1CachedNode744_valid⟩

def s1CachedNode864 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode863

theorem s1CachedNode864_valid : s1CachedNode864.Valid := ⟨s1CachedNode2_valid,s1CachedNode863_valid⟩

def s1CachedNode865 : CachedPolynomialExpr 9 := .add s1CachedNode860 s1CachedNode864

theorem s1CachedNode865_valid : s1CachedNode865.Valid := ⟨s1CachedNode860_valid,s1CachedNode864_valid⟩

def s1CachedNode866 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode865

theorem s1CachedNode866_valid : s1CachedNode866.Valid := ⟨s1CachedNode1_valid,s1CachedNode865_valid⟩

def s1CachedNode867 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode751

theorem s1CachedNode867_valid : s1CachedNode867.Valid := ⟨s1CachedNode27_valid,s1CachedNode751_valid⟩

def s1CachedNode868 : CachedPolynomialExpr 9 := .add s1CachedNode750 s1CachedNode867

theorem s1CachedNode868_valid : s1CachedNode868.Valid := ⟨s1CachedNode750_valid,s1CachedNode867_valid⟩

def s1CachedNode869 : CachedPolynomialExpr 9 := .mul s1CachedNode321 s1CachedNode34

theorem s1CachedNode869_valid : s1CachedNode869.Valid := ⟨s1CachedNode321_valid,s1CachedNode34_valid⟩

def s1CachedNode870 : CachedPolynomialExpr 9 := .mul s1CachedNode869 s1CachedNode178

theorem s1CachedNode870_valid : s1CachedNode870.Valid := ⟨s1CachedNode869_valid,s1CachedNode178_valid⟩

def s1CachedNode871 : CachedPolynomialExpr 9 := .add s1CachedNode835 s1CachedNode870

theorem s1CachedNode871_valid : s1CachedNode871.Valid := ⟨s1CachedNode835_valid,s1CachedNode870_valid⟩

def s1CachedNode872 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode871

theorem s1CachedNode872_valid : s1CachedNode872.Valid := ⟨s1CachedNode178_valid,s1CachedNode871_valid⟩

def s1CachedNode873 : CachedPolynomialExpr 9 := .add s1CachedNode868 s1CachedNode872

theorem s1CachedNode873_valid : s1CachedNode873.Valid := ⟨s1CachedNode868_valid,s1CachedNode872_valid⟩

def s1CachedNode874 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode681

theorem s1CachedNode874_valid : s1CachedNode874.Valid := ⟨s1CachedNode4_valid,s1CachedNode681_valid⟩

def s1CachedNode875 : CachedPolynomialExpr 9 := .add s1CachedNode674 s1CachedNode874

theorem s1CachedNode875_valid : s1CachedNode875.Valid := ⟨s1CachedNode674_valid,s1CachedNode874_valid⟩

def s1CachedNode876 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode875

theorem s1CachedNode876_valid : s1CachedNode876.Valid := ⟨s1CachedNode81_valid,s1CachedNode875_valid⟩

def s1CachedNode877 : CachedPolynomialExpr 9 := .add s1CachedNode873 s1CachedNode876

theorem s1CachedNode877_valid : s1CachedNode877.Valid := ⟨s1CachedNode873_valid,s1CachedNode876_valid⟩

def s1CachedNode878 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode877

theorem s1CachedNode878_valid : s1CachedNode878.Valid := ⟨s1CachedNode4_valid,s1CachedNode877_valid⟩

def s1CachedNode879 : CachedPolynomialExpr 9 := .mul s1CachedNode502 s1CachedNode724

theorem s1CachedNode879_valid : s1CachedNode879.Valid := ⟨s1CachedNode502_valid,s1CachedNode724_valid⟩

def s1CachedNode880 : CachedPolynomialExpr 9 := .add s1CachedNode722 s1CachedNode879

theorem s1CachedNode880_valid : s1CachedNode880.Valid := ⟨s1CachedNode722_valid,s1CachedNode879_valid⟩

def s1CachedNode881 : CachedPolynomialExpr 9 := .mul s1CachedNode77 s1CachedNode880

theorem s1CachedNode881_valid : s1CachedNode881.Valid := ⟨s1CachedNode77_valid,s1CachedNode880_valid⟩

def s1CachedNode882 : CachedPolynomialExpr 9 := .add s1CachedNode878 s1CachedNode881

theorem s1CachedNode882_valid : s1CachedNode882.Valid := ⟨s1CachedNode878_valid,s1CachedNode881_valid⟩

def s1CachedNode883 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode882

theorem s1CachedNode883_valid : s1CachedNode883.Valid := ⟨s1CachedNode2_valid,s1CachedNode882_valid⟩

def s1CachedNode884 : CachedPolynomialExpr 9 := .add s1CachedNode866 s1CachedNode883

theorem s1CachedNode884_valid : s1CachedNode884.Valid := ⟨s1CachedNode866_valid,s1CachedNode883_valid⟩

def s1CachedHessian12 : CachedPolynomialExpr 9 := s1CachedNode884

theorem s1CachedHessian12_valid : s1CachedHessian12.Valid := s1CachedNode884_valid

theorem s1CachedHessian12_erase : s1CachedHessian12.erase = s1HornerHessian12 := by decide +kernel

def s1CachedHessian20 : CachedPolynomialExpr 9 := s1CachedNode765

theorem s1CachedHessian20_valid : s1CachedHessian20.Valid := s1CachedNode765_valid

theorem s1CachedHessian20_erase : s1CachedHessian20.erase = s1HornerHessian20 := by decide +kernel

def s1CachedHessian21 : CachedPolynomialExpr 9 := s1CachedNode884

theorem s1CachedHessian21_valid : s1CachedHessian21.Valid := s1CachedNode884_valid

theorem s1CachedHessian21_erase : s1CachedHessian21.erase = s1HornerHessian21 := by decide +kernel

def s1CachedNode885 : CachedPolynomialExpr 9 := .mul s1CachedNode609 s1CachedNode34

theorem s1CachedNode885_valid : s1CachedNode885.Valid := ⟨s1CachedNode609_valid,s1CachedNode34_valid⟩

def s1CachedNode886 : CachedPolynomialExpr 9 := .mul s1CachedNode885 s1CachedNode4

theorem s1CachedNode886_valid : s1CachedNode886.Valid := ⟨s1CachedNode885_valid,s1CachedNode4_valid⟩

def s1CachedNode887 : CachedPolynomialExpr 9 := .mul s1CachedNode611 s1CachedNode34

theorem s1CachedNode887_valid : s1CachedNode887.Valid := ⟨s1CachedNode611_valid,s1CachedNode34_valid⟩

def s1CachedNode888 : CachedPolynomialExpr 9 := .mul s1CachedNode887 s1CachedNode1

theorem s1CachedNode888_valid : s1CachedNode888.Valid := ⟨s1CachedNode887_valid,s1CachedNode1_valid⟩

def s1CachedNode889 : CachedPolynomialExpr 9 := .mul s1CachedNode888 s1CachedNode4

theorem s1CachedNode889_valid : s1CachedNode889.Valid := ⟨s1CachedNode888_valid,s1CachedNode4_valid⟩

def s1CachedNode890 : CachedPolynomialExpr 9 := .add s1CachedNode886 s1CachedNode889

theorem s1CachedNode890_valid : s1CachedNode890.Valid := ⟨s1CachedNode886_valid,s1CachedNode889_valid⟩

def s1CachedNode891 : CachedPolynomialExpr 9 := .add s1CachedNode890 s1CachedNode736

theorem s1CachedNode891_valid : s1CachedNode891.Valid := ⟨s1CachedNode890_valid,s1CachedNode736_valid⟩

def s1CachedNode892 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode891

theorem s1CachedNode892_valid : s1CachedNode892.Valid := ⟨s1CachedNode1_valid,s1CachedNode891_valid⟩

def s1CachedNode893 : CachedPolynomialExpr 9 := .add s1CachedNode892 s1CachedNode776

theorem s1CachedNode893_valid : s1CachedNode893.Valid := ⟨s1CachedNode892_valid,s1CachedNode776_valid⟩

def s1CachedNode894 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode893

theorem s1CachedNode894_valid : s1CachedNode894.Valid := ⟨s1CachedNode1_valid,s1CachedNode893_valid⟩

def s1CachedNode895 : CachedPolynomialExpr 9 := .mul s1CachedNode589 s1CachedNode47

theorem s1CachedNode895_valid : s1CachedNode895.Valid := ⟨s1CachedNode589_valid,s1CachedNode47_valid⟩

def s1CachedNode896 : CachedPolynomialExpr 9 := .add s1CachedNode895 s1CachedNode569

theorem s1CachedNode896_valid : s1CachedNode896.Valid := ⟨s1CachedNode895_valid,s1CachedNode569_valid⟩

def s1CachedNode897 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode896

theorem s1CachedNode897_valid : s1CachedNode897.Valid := ⟨s1CachedNode4_valid,s1CachedNode896_valid⟩

def s1CachedNode898 : CachedPolynomialExpr 9 := .add s1CachedNode626 s1CachedNode897

theorem s1CachedNode898_valid : s1CachedNode898.Valid := ⟨s1CachedNode626_valid,s1CachedNode897_valid⟩

def s1CachedNode899 : CachedPolynomialExpr 9 := .add s1CachedNode898 s1CachedNode635

theorem s1CachedNode899_valid : s1CachedNode899.Valid := ⟨s1CachedNode898_valid,s1CachedNode635_valid⟩

def s1CachedNode900 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode899

theorem s1CachedNode900_valid : s1CachedNode900.Valid := ⟨s1CachedNode4_valid,s1CachedNode899_valid⟩

def s1CachedNode901 : CachedPolynomialExpr 9 := .add s1CachedNode738 s1CachedNode900

theorem s1CachedNode901_valid : s1CachedNode901.Valid := ⟨s1CachedNode738_valid,s1CachedNode900_valid⟩

def s1CachedNode902 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode901

theorem s1CachedNode902_valid : s1CachedNode902.Valid := ⟨s1CachedNode2_valid,s1CachedNode901_valid⟩

def s1CachedNode903 : CachedPolynomialExpr 9 := .add s1CachedNode894 s1CachedNode902

theorem s1CachedNode903_valid : s1CachedNode903.Valid := ⟨s1CachedNode894_valid,s1CachedNode902_valid⟩

def s1CachedNode904 : CachedPolynomialExpr 9 := .mul s1CachedNode603 s1CachedNode34

theorem s1CachedNode904_valid : s1CachedNode904.Valid := ⟨s1CachedNode603_valid,s1CachedNode34_valid⟩

def s1CachedNode905 : CachedPolynomialExpr 9 := .add s1CachedNode596 s1CachedNode904

theorem s1CachedNode905_valid : s1CachedNode905.Valid := ⟨s1CachedNode596_valid,s1CachedNode904_valid⟩

def s1CachedNode906 : CachedPolynomialExpr 9 := .add s1CachedNode905 s1CachedNode598

theorem s1CachedNode906_valid : s1CachedNode906.Valid := ⟨s1CachedNode905_valid,s1CachedNode598_valid⟩

def s1CachedNode907 : CachedPolynomialExpr 9 := .add s1CachedNode600 s1CachedNode650

theorem s1CachedNode907_valid : s1CachedNode907.Valid := ⟨s1CachedNode600_valid,s1CachedNode650_valid⟩

def s1CachedNode908 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode907

theorem s1CachedNode908_valid : s1CachedNode908.Valid := ⟨s1CachedNode20_valid,s1CachedNode907_valid⟩

def s1CachedNode909 : CachedPolynomialExpr 9 := .add s1CachedNode906 s1CachedNode908

theorem s1CachedNode909_valid : s1CachedNode909.Valid := ⟨s1CachedNode906_valid,s1CachedNode908_valid⟩

def s1CachedNode910 : CachedPolynomialExpr 9 := .add s1CachedNode255 s1CachedNode337

theorem s1CachedNode910_valid : s1CachedNode910.Valid := ⟨s1CachedNode255_valid,s1CachedNode337_valid⟩

def s1CachedNode911 : CachedPolynomialExpr 9 := .mul s1CachedNode20 s1CachedNode910

theorem s1CachedNode911_valid : s1CachedNode911.Valid := ⟨s1CachedNode20_valid,s1CachedNode910_valid⟩

def s1CachedNode912 : CachedPolynomialExpr 9 := .add s1CachedNode910 s1CachedNode911

theorem s1CachedNode912_valid : s1CachedNode912.Valid := ⟨s1CachedNode910_valid,s1CachedNode911_valid⟩

def s1CachedNode913 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode912

theorem s1CachedNode913_valid : s1CachedNode913.Valid := ⟨s1CachedNode178_valid,s1CachedNode912_valid⟩

def s1CachedNode914 : CachedPolynomialExpr 9 := .add s1CachedNode654 s1CachedNode913

theorem s1CachedNode914_valid : s1CachedNode914.Valid := ⟨s1CachedNode654_valid,s1CachedNode913_valid⟩

def s1CachedNode915 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode914

theorem s1CachedNode915_valid : s1CachedNode915.Valid := ⟨s1CachedNode178_valid,s1CachedNode914_valid⟩

def s1CachedNode916 : CachedPolynomialExpr 9 := .add s1CachedNode909 s1CachedNode915

theorem s1CachedNode916_valid : s1CachedNode916.Valid := ⟨s1CachedNode909_valid,s1CachedNode915_valid⟩

def s1CachedNode917 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode788

theorem s1CachedNode917_valid : s1CachedNode917.Valid := ⟨s1CachedNode4_valid,s1CachedNode788_valid⟩

def s1CachedNode918 : CachedPolynomialExpr 9 := .add s1CachedNode786 s1CachedNode917

theorem s1CachedNode918_valid : s1CachedNode918.Valid := ⟨s1CachedNode786_valid,s1CachedNode917_valid⟩

def s1CachedNode919 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode918

theorem s1CachedNode919_valid : s1CachedNode919.Valid := ⟨s1CachedNode81_valid,s1CachedNode918_valid⟩

def s1CachedNode920 : CachedPolynomialExpr 9 := .add s1CachedNode916 s1CachedNode919

theorem s1CachedNode920_valid : s1CachedNode920.Valid := ⟨s1CachedNode916_valid,s1CachedNode919_valid⟩

def s1CachedNode921 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode920

theorem s1CachedNode921_valid : s1CachedNode921.Valid := ⟨s1CachedNode4_valid,s1CachedNode920_valid⟩

def s1CachedNode922 : CachedPolynomialExpr 9 := .add s1CachedNode903 s1CachedNode921

theorem s1CachedNode922_valid : s1CachedNode922.Valid := ⟨s1CachedNode903_valid,s1CachedNode921_valid⟩

def s1CachedNode923 : CachedPolynomialExpr 9 := .mul s1CachedNode1 s1CachedNode922

theorem s1CachedNode923_valid : s1CachedNode923.Valid := ⟨s1CachedNode1_valid,s1CachedNode922_valid⟩

def s1CachedNode924 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode907

theorem s1CachedNode924_valid : s1CachedNode924.Valid := ⟨s1CachedNode27_valid,s1CachedNode907_valid⟩

def s1CachedNode925 : CachedPolynomialExpr 9 := .add s1CachedNode906 s1CachedNode924

theorem s1CachedNode925_valid : s1CachedNode925.Valid := ⟨s1CachedNode906_valid,s1CachedNode924_valid⟩

def s1CachedNode926 : CachedPolynomialExpr 9 := .mul s1CachedNode27 s1CachedNode910

theorem s1CachedNode926_valid : s1CachedNode926.Valid := ⟨s1CachedNode27_valid,s1CachedNode910_valid⟩

def s1CachedNode927 : CachedPolynomialExpr 9 := .add s1CachedNode910 s1CachedNode926

theorem s1CachedNode927_valid : s1CachedNode927.Valid := ⟨s1CachedNode910_valid,s1CachedNode926_valid⟩

def s1CachedNode928 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode927

theorem s1CachedNode928_valid : s1CachedNode928.Valid := ⟨s1CachedNode178_valid,s1CachedNode927_valid⟩

def s1CachedNode929 : CachedPolynomialExpr 9 := .add s1CachedNode835 s1CachedNode928

theorem s1CachedNode929_valid : s1CachedNode929.Valid := ⟨s1CachedNode835_valid,s1CachedNode928_valid⟩

def s1CachedNode930 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode929

theorem s1CachedNode930_valid : s1CachedNode930.Valid := ⟨s1CachedNode178_valid,s1CachedNode929_valid⟩

def s1CachedNode931 : CachedPolynomialExpr 9 := .add s1CachedNode925 s1CachedNode930

theorem s1CachedNode931_valid : s1CachedNode931.Valid := ⟨s1CachedNode925_valid,s1CachedNode930_valid⟩

def s1CachedNode932 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode554

theorem s1CachedNode932_valid : s1CachedNode932.Valid := ⟨s1CachedNode4_valid,s1CachedNode554_valid⟩

def s1CachedNode933 : CachedPolynomialExpr 9 := .add s1CachedNode566 s1CachedNode932

theorem s1CachedNode933_valid : s1CachedNode933.Valid := ⟨s1CachedNode566_valid,s1CachedNode932_valid⟩

def s1CachedNode934 : CachedPolynomialExpr 9 := .mul s1CachedNode81 s1CachedNode933

theorem s1CachedNode934_valid : s1CachedNode934.Valid := ⟨s1CachedNode81_valid,s1CachedNode933_valid⟩

def s1CachedNode935 : CachedPolynomialExpr 9 := .add s1CachedNode931 s1CachedNode934

theorem s1CachedNode935_valid : s1CachedNode935.Valid := ⟨s1CachedNode931_valid,s1CachedNode934_valid⟩

def s1CachedNode936 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode935

theorem s1CachedNode936_valid : s1CachedNode936.Valid := ⟨s1CachedNode4_valid,s1CachedNode935_valid⟩

def s1CachedNode937 : CachedPolynomialExpr 9 := .mul s1CachedNode887 s1CachedNode2

theorem s1CachedNode937_valid : s1CachedNode937.Valid := ⟨s1CachedNode887_valid,s1CachedNode2_valid⟩

def s1CachedNode938 : CachedPolynomialExpr 9 := .mul s1CachedNode937 s1CachedNode4

theorem s1CachedNode938_valid : s1CachedNode938.Valid := ⟨s1CachedNode937_valid,s1CachedNode4_valid⟩

def s1CachedNode939 : CachedPolynomialExpr 9 := .add s1CachedNode886 s1CachedNode938

theorem s1CachedNode939_valid : s1CachedNode939.Valid := ⟨s1CachedNode886_valid,s1CachedNode938_valid⟩

def s1CachedNode940 : CachedPolynomialExpr 9 := .mul s1CachedNode77 s1CachedNode939

theorem s1CachedNode940_valid : s1CachedNode940.Valid := ⟨s1CachedNode77_valid,s1CachedNode939_valid⟩

def s1CachedNode941 : CachedPolynomialExpr 9 := .add s1CachedNode936 s1CachedNode940

theorem s1CachedNode941_valid : s1CachedNode941.Valid := ⟨s1CachedNode936_valid,s1CachedNode940_valid⟩

def s1CachedNode942 : CachedPolynomialExpr 9 := .mul s1CachedNode2 s1CachedNode941

theorem s1CachedNode942_valid : s1CachedNode942.Valid := ⟨s1CachedNode2_valid,s1CachedNode941_valid⟩

def s1CachedNode943 : CachedPolynomialExpr 9 := .add s1CachedNode923 s1CachedNode942

theorem s1CachedNode943_valid : s1CachedNode943.Valid := ⟨s1CachedNode923_valid,s1CachedNode942_valid⟩

def s1CachedNode944 : CachedPolynomialExpr 9 := .add s1CachedNode538 s1CachedNode315

theorem s1CachedNode944_valid : s1CachedNode944.Valid := ⟨s1CachedNode538_valid,s1CachedNode315_valid⟩

def s1CachedNode945 : CachedPolynomialExpr 9 := .mul s1CachedNode34 s1CachedNode944

theorem s1CachedNode945_valid : s1CachedNode945.Valid := ⟨s1CachedNode34_valid,s1CachedNode944_valid⟩

def s1CachedNode946 : CachedPolynomialExpr 9 := .add s1CachedNode537 s1CachedNode945

theorem s1CachedNode946_valid : s1CachedNode946.Valid := ⟨s1CachedNode537_valid,s1CachedNode945_valid⟩

def s1CachedNode947 : CachedPolynomialExpr 9 := .mul s1CachedNode543 s1CachedNode34

theorem s1CachedNode947_valid : s1CachedNode947.Valid := ⟨s1CachedNode543_valid,s1CachedNode34_valid⟩

def s1CachedNode948 : CachedPolynomialExpr 9 := .add s1CachedNode542 s1CachedNode947

theorem s1CachedNode948_valid : s1CachedNode948.Valid := ⟨s1CachedNode542_valid,s1CachedNode947_valid⟩

def s1CachedNode949 : CachedPolynomialExpr 9 := .mul s1CachedNode547 s1CachedNode34

theorem s1CachedNode949_valid : s1CachedNode949.Valid := ⟨s1CachedNode547_valid,s1CachedNode34_valid⟩

def s1CachedNode950 : CachedPolynomialExpr 9 := .add s1CachedNode546 s1CachedNode949

theorem s1CachedNode950_valid : s1CachedNode950.Valid := ⟨s1CachedNode546_valid,s1CachedNode949_valid⟩

def s1CachedNode951 : CachedPolynomialExpr 9 := .mul s1CachedNode550 s1CachedNode4

theorem s1CachedNode951_valid : s1CachedNode951.Valid := ⟨s1CachedNode550_valid,s1CachedNode4_valid⟩

def s1CachedNode952 : CachedPolynomialExpr 9 := .add s1CachedNode950 s1CachedNode951

theorem s1CachedNode952_valid : s1CachedNode952.Valid := ⟨s1CachedNode950_valid,s1CachedNode951_valid⟩

def s1CachedNode953 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode952

theorem s1CachedNode953_valid : s1CachedNode953.Valid := ⟨s1CachedNode4_valid,s1CachedNode952_valid⟩

def s1CachedNode954 : CachedPolynomialExpr 9 := .add s1CachedNode948 s1CachedNode953

theorem s1CachedNode954_valid : s1CachedNode954.Valid := ⟨s1CachedNode948_valid,s1CachedNode953_valid⟩

def s1CachedNode955 : CachedPolynomialExpr 9 := .mul s1CachedNode579 s1CachedNode34

theorem s1CachedNode955_valid : s1CachedNode955.Valid := ⟨s1CachedNode579_valid,s1CachedNode34_valid⟩

def s1CachedNode956 : CachedPolynomialExpr 9 := .mul s1CachedNode25 s1CachedNode34

theorem s1CachedNode956_valid : s1CachedNode956.Valid := ⟨s1CachedNode25_valid,s1CachedNode34_valid⟩

def s1CachedNode957 : CachedPolynomialExpr 9 := .mul s1CachedNode956 s1CachedNode34

theorem s1CachedNode957_valid : s1CachedNode957.Valid := ⟨s1CachedNode956_valid,s1CachedNode34_valid⟩

def s1CachedNode958 : CachedPolynomialExpr 9 := .mul s1CachedNode256 s1CachedNode957

theorem s1CachedNode958_valid : s1CachedNode958.Valid := ⟨s1CachedNode256_valid,s1CachedNode957_valid⟩

def s1CachedNode959 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode958

theorem s1CachedNode959_valid : s1CachedNode959.Valid := ⟨s1CachedNode260_valid,s1CachedNode958_valid⟩

def s1CachedNode960 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode959

theorem s1CachedNode960_valid : s1CachedNode960.Valid := ⟨s1CachedNode178_valid,s1CachedNode959_valid⟩

def s1CachedNode961 : CachedPolynomialExpr 9 := .add s1CachedNode955 s1CachedNode960

theorem s1CachedNode961_valid : s1CachedNode961.Valid := ⟨s1CachedNode955_valid,s1CachedNode960_valid⟩

def s1CachedNode962 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode961

theorem s1CachedNode962_valid : s1CachedNode962.Valid := ⟨s1CachedNode178_valid,s1CachedNode961_valid⟩

def s1CachedNode963 : CachedPolynomialExpr 9 := .add s1CachedNode954 s1CachedNode962

theorem s1CachedNode963_valid : s1CachedNode963.Valid := ⟨s1CachedNode954_valid,s1CachedNode962_valid⟩

def s1CachedNode964 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode963

theorem s1CachedNode964_valid : s1CachedNode964.Valid := ⟨s1CachedNode4_valid,s1CachedNode963_valid⟩

def s1CachedNode965 : CachedPolynomialExpr 9 := .add s1CachedNode946 s1CachedNode964

theorem s1CachedNode965_valid : s1CachedNode965.Valid := ⟨s1CachedNode946_valid,s1CachedNode964_valid⟩

def s1CachedNode966 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode339

theorem s1CachedNode966_valid : s1CachedNode966.Valid := ⟨s1CachedNode260_valid,s1CachedNode339_valid⟩

def s1CachedNode967 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode966

theorem s1CachedNode967_valid : s1CachedNode967.Valid := ⟨s1CachedNode178_valid,s1CachedNode966_valid⟩

def s1CachedNode968 : CachedPolynomialExpr 9 := .add s1CachedNode260 s1CachedNode967

theorem s1CachedNode968_valid : s1CachedNode968.Valid := ⟨s1CachedNode260_valid,s1CachedNode967_valid⟩

def s1CachedNode969 : CachedPolynomialExpr 9 := .mul s1CachedNode178 s1CachedNode968

theorem s1CachedNode969_valid : s1CachedNode969.Valid := ⟨s1CachedNode178_valid,s1CachedNode968_valid⟩

def s1CachedNode970 : CachedPolynomialExpr 9 := .add s1CachedNode965 s1CachedNode969

theorem s1CachedNode970_valid : s1CachedNode970.Valid := ⟨s1CachedNode965_valid,s1CachedNode969_valid⟩

def s1CachedNode971 : CachedPolynomialExpr 9 := .mul s1CachedNode4 s1CachedNode970

theorem s1CachedNode971_valid : s1CachedNode971.Valid := ⟨s1CachedNode4_valid,s1CachedNode970_valid⟩

def s1CachedNode972 : CachedPolynomialExpr 9 := .add s1CachedNode943 s1CachedNode971

theorem s1CachedNode972_valid : s1CachedNode972.Valid := ⟨s1CachedNode943_valid,s1CachedNode971_valid⟩

def s1CachedHessian22 : CachedPolynomialExpr 9 := s1CachedNode972

theorem s1CachedHessian22_valid : s1CachedHessian22.Valid := s1CachedNode972_valid

theorem s1CachedHessian22_erase : s1CachedHessian22.erase = s1HornerHessian22 := by decide +kernel

end SparseLowerTail.Section05
