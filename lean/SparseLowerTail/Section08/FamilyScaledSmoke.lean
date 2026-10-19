import SparseLowerTail.Section08.FamilyOffsetCover

/-! Two selected mixed-contact Hessian boxes. Not a full cover. -/
namespace SparseLowerTail.Certificate.FamilyScaledSmoke
open Numerics Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Leaf0
def logLower : ExpEndpointCertificate :=
  ⟨(39/10 : ℚ),20,(903525595301201735/1152921504606846976 : ℚ),(112940699412650217/144115188075855872 : ℚ),(2917166875026919/144115188075855872 : ℚ),(11668667500107677/576460752303423488 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate :=
  ⟨(2503/640 : ℚ),20,(451454080956067807/576460752303423488 : ℚ),(902908161912135615/1152921504606846976 : ℚ),(23083473733211521/1152921504606846976 : ℚ),(11541736866605761/576460752303423488 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate :=
  ⟨(93741710288170351/576460752303423488 : ℚ),20,(1141263136070990353/1152921504606846976 : ℚ),(570631568035495177/576460752303423488 : ℚ),(979888209452753657/1152921504606846976 : ℚ),(122486026181594209/144115188075855872 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate :=
  ⟨(95081148923186273/576460752303423488 : ℚ),20,(570548705664806987/576460752303423488 : ℚ),(1141097411329613975/1152921504606846976 : ℚ),(977614027789409959/1152921504606846976 : ℚ),(977614027789409973/1152921504606846976 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower0 : ExpEndpointCertificate :=
  ⟨(11421462845205898027/2882303761517117440 : ℚ),20,(449998280448448207/576460752303423488 : ℚ),(899996560896896415/1152921504606846976 : ℚ),(21920855578214159/1152921504606846976 : ℚ),(21920855578214161/1152921504606846976 : ℚ)⟩
theorem qLower0_valid : qLower0.Valid := by decide +kernel
def qUpper0 : ExpEndpointCertificate :=
  ⟨(11477699634282053093/2882303761517117440 : ℚ),20,(449449868551259149/576460752303423488 : ℚ),(898899737102518299/1152921504606846976 : ℚ),(21497301970740787/1152921504606846976 : ℚ),(5374325492685197/288230376151711744 : ℚ)⟩
theorem qUpper0_valid : qUpper0.Valid := by decide +kernel
def pLower01 : ExpEndpointCertificate :=
  ⟨(5800970510247519019/2882303761517117440 : ℚ),20,(508323858676944307/576460752303423488 : ℚ),(1016647717353888615/1152921504606846976 : ℚ),(77037422679242699/576460752303423488 : ℚ),(154074845358485401/1152921504606846976 : ℚ)⟩
theorem pLower01_valid : pLower01.Valid := by decide +kernel
def pUpper01 : ExpEndpointCertificate :=
  ⟨(5850451899882618341/2882303761517117440 : ℚ),20,(1015557483464250961/1152921504606846976 : ℚ),(507778741732125481/576460752303423488 : ℚ),(151452370219056995/1152921504606846976 : ℚ),(75726185109528499/576460752303423488 : ℚ)⟩
theorem pUpper01_valid : pUpper01.Valid := by decide +kernel
def pLower02 : ExpEndpointCertificate :=
  ⟨(5800970510247519019/2882303761517117440 : ℚ),20,(508323858676944307/576460752303423488 : ℚ),(1016647717353888615/1152921504606846976 : ℚ),(77037422679242699/576460752303423488 : ℚ),(154074845358485401/1152921504606846976 : ℚ)⟩
theorem pLower02_valid : pLower02.Valid := by decide +kernel
def pUpper02 : ExpEndpointCertificate :=
  ⟨(5850451899882618341/2882303761517117440 : ℚ),20,(1015557483464250961/1152921504606846976 : ℚ),(507778741732125481/576460752303423488 : ℚ),(151452370219056995/1152921504606846976 : ℚ),(75726185109528499/576460752303423488 : ℚ)⟩
theorem pUpper02_valid : pUpper02.Valid := by decide +kernel
def qLower1 : ExpEndpointCertificate :=
  ⟨(180478175289140011/2882303761517117440 : ℚ),20,(287104591869456667/288230376151711744 : ℚ),(1148418367477826669/1152921504606846976 : ℚ),(541471976026201129/576460752303423488 : ℚ),(541471976026201137/576460752303423488 : ℚ)⟩
theorem qLower1_valid : qLower1.Valid := by decide +kernel
def qUpper1 : ExpEndpointCertificate :=
  ⟨(223204165483183589/2882303761517117440 : ℚ),20,(17927420038674901/18014398509481984 : ℚ),(1147354882475193665/1152921504606846976 : ℚ),(533504634120834165/576460752303423488 : ℚ),(533504634120834173/576460752303423488 : ℚ)⟩
theorem qUpper1_valid : qUpper1.Valid := by decide +kernel
def pLower12 : ExpEndpointCertificate :=
  ⟨(180478175289140011/2882303761517117440 : ℚ),20,(287104591869456667/288230376151711744 : ℚ),(1148418367477826669/1152921504606846976 : ℚ),(541471976026201129/576460752303423488 : ℚ),(541471976026201137/576460752303423488 : ℚ)⟩
theorem pLower12_valid : pLower12.Valid := by decide +kernel
def pUpper12 : ExpEndpointCertificate :=
  ⟨(223204165483183589/2882303761517117440 : ℚ),20,(17927420038674901/18014398509481984 : ℚ),(1147354882475193665/1152921504606846976 : ℚ),(533504634120834165/576460752303423488 : ℚ),(533504634120834173/576460752303423488 : ℚ)⟩
theorem pUpper12_valid : pUpper12.Valid := by decide +kernel
def qLower2 : ExpEndpointCertificate :=
  ⟨(180478175289140011/2882303761517117440 : ℚ),20,(287104591869456667/288230376151711744 : ℚ),(1148418367477826669/1152921504606846976 : ℚ),(541471976026201129/576460752303423488 : ℚ),(541471976026201137/576460752303423488 : ℚ)⟩
theorem qLower2_valid : qLower2.Valid := by decide +kernel
def qUpper2 : ExpEndpointCertificate :=
  ⟨(223204165483183589/2882303761517117440 : ℚ),20,(17927420038674901/18014398509481984 : ℚ),(1147354882475193665/1152921504606846976 : ℚ),(533504634120834165/576460752303423488 : ℚ),(533504634120834173/576460752303423488 : ℚ)⟩
theorem qUpper2_valid : qUpper2.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨187483420576340702,190162297846372546⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def box : FamilyBoxCertificate :=
  ⟨parameter,![⟨-27770674008510050,-26974820695189849⟩,⟨54787675100396719,56323730049714611⟩,⟨2223059054073101,2275205846062502⟩,⟨-4734159318636921,-4594233856076890⟩,⟨26711806132411047,27134888770390998⟩,⟨-53402604796012274,-51896662886233548⟩,⟨301737708911472848,306088925965036039⟩],
    ![qLower0,qLower1,qLower2],![qUpper0,qUpper1,qUpper2]⟩
theorem box_valid : box.Valid := by
  refine ⟨parameter_valid,?_,?_,?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact qLower0_valid
    · exact qLower1_valid
    · exact qLower2_valid
  · intro i; fin_cases i
    · exact qUpper0_valid
    · exact qUpper1_valid
    · exact qUpper2_valid
def pairLower : Fin 3 → Fin 3 → ExpEndpointCertificate :=
  ![![qLower0,pLower01,pLower02],![pLower01,qLower1,pLower12],![pLower02,pLower12,qLower2]]
def pairUpper : Fin 3 → Fin 3 → ExpEndpointCertificate :=
  ![![qUpper0,pUpper01,pUpper02],![pUpper01,qUpper1,pUpper12],![pUpper02,pUpper12,qUpper2]]
def certificate : FamilyScaledBoxCertificate := ⟨box,pairLower,pairUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨box_valid,?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  · exact ⟨pLower01_valid,pUpper01_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower02_valid,pUpper02_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower01_valid,pUpper01_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower12_valid,pUpper12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower02_valid,pUpper02_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower12_valid,pUpper12_valid,by decide +kernel,by decide +kernel⟩
def transform : FamilyRationalMatrix := ![![(1603753/1000000 : ℚ),(-22317/40000 : ℚ),(-215637/125000 : ℚ)],![(0/1 : ℚ),(4451249/1000000 : ℚ),(30809/5000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(7601407/1000000 : ℚ)]]
theorem margins_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.hessianIntervals transform) := by decide +kernel
theorem hessian_positive {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (parameter.logLower.q : ℝ) (parameter.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((box.qLower i).q : ℝ) ((box.qUpper i).q : ℝ))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  certificate.hessian_positive certificate_valid transform margins_checked hz hL hq hv
def offsetBox : ReplayBox 4 := ⟨![(39/10 : ℚ), (-1/10 : ℚ), (-1/10 : ℚ), (-1/10 : ℚ)],![(2503/640 : ℚ), (-3/32 : ℚ), (-7/80 : ℚ), (-7/80 : ℚ)]⟩
theorem encloses_offsets : box.EnclosesABBOffsets offsetBox := by decide +kernel
theorem offset_hessian_positive {z : ℝ} (hz : 0<z) (hz1 : z<1)
    {q : FamilyVector} (hq : offsetBox.Contains (familyABBOffsetCoordinates z q))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  certificate.abb_offset_hessian_positive certificate_valid transform margins_checked
    encloses_offsets hz hz1 hq hv
end Leaf0

namespace Leaf1
def logLower : ExpEndpointCertificate :=
  ⟨(949/100 : ℚ),20,(637101789975478221/1152921504606846976 : ℚ),(318550894987739111/576460752303423488 : ℚ),(21791399128341/288230376151711744 : ℚ),(87165596513365/1152921504606846976 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate :=
  ⟨(19/2 : ℚ),20,(636703725764767213/1152921504606846976 : ℚ),(318351862882383607/576460752303423488 : ℚ),(86298284336703/1152921504606846976 : ℚ),(1348410692761/18014398509481984 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate :=
  ⟨(409546667518025/288230376151711744 : ℚ),20,(288204780621530565/288230376151711744 : ℚ),(1152819122486122261/1152921504606846976 : ℚ),(143910560154476277/144115188075855872 : ℚ),(1151284481235810233/1152921504606846976 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate :=
  ⟨(828198392536621/576460752303423488 : ℚ),20,(1152817984455565199/1152921504606846976 : ℚ),(72051124028472825/72057594037927936 : ℚ),(1151266297120802623/1152921504606846976 : ℚ),(71954143570050165/72057594037927936 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower0 : ExpEndpointCertificate :=
  ⟨(67672319468302282529/7205759403792793600 : ℚ),20,(641039214687304981/1152921504606846976 : ℚ),(320519607343652491/576460752303423488 : ℚ),(12024512511081/144115188075855872 : ℚ),(96196100088649/1152921504606846976 : ℚ)⟩
theorem qLower0_valid : qLower0.Valid := by decide +kernel
def qUpper0 : ExpEndpointCertificate :=
  ⟨(135633096939193791077/14411518807585587200 : ℚ),20,(160059446061725015/288230376151711744 : ℚ),(640237784246900061/1152921504606846976 : ℚ),(47144900193965/576460752303423488 : ℚ),(94289800387931/1152921504606846976 : ℚ)⟩
theorem qUpper0_valid : qUpper0.Valid := by decide +kernel
def pLower01 : ExpEndpointCertificate :=
  ⟨(33480991097305476897/7205759403792793600 : ℚ),20,(431171512528973359/576460752303423488 : ℚ),(862343025057946719/1152921504606846976 : ℚ),(2765825592288225/288230376151711744 : ℚ),(5531651184576451/576460752303423488 : ℚ)⟩
theorem pLower01_valid : pLower01.Valid := by decide +kernel
def pUpper01 : ExpEndpointCertificate :=
  ⟨(67178382603162251877/14411518807585587200 : ℚ),20,(861534106829858907/1152921504606846976 : ℚ),(215383526707464727/288230376151711744 : ℚ),(1362302389506293/144115188075855872 : ℚ),(5449209558025173/576460752303423488 : ℚ)⟩
theorem pUpper01_valid : pUpper01.Valid := by decide +kernel
def pLower02 : ExpEndpointCertificate :=
  ⟨(33480991097305476897/7205759403792793600 : ℚ),20,(431171512528973359/576460752303423488 : ℚ),(862343025057946719/1152921504606846976 : ℚ),(2765825592288225/288230376151711744 : ℚ),(5531651184576451/576460752303423488 : ℚ)⟩
theorem pLower02_valid : pLower02.Valid := by decide +kernel
def pUpper02 : ExpEndpointCertificate :=
  ⟨(67178382603162251877/14411518807585587200 : ℚ),20,(861534106829858907/1152921504606846976 : ℚ),(215383526707464727/288230376151711744 : ℚ),(1362302389506293/144115188075855872 : ℚ),(5449209558025173/576460752303423488 : ℚ)⟩
theorem pUpper02_valid : pUpper02.Valid := by decide +kernel
def qLower1 : ExpEndpointCertificate :=
  ⟨(-142067454738265747/1441151880758558720 : ℚ),20,(1160046804981862739/1152921504606846976 : ℚ),(290011701245465685/288230376151711744 : ℚ),(1272366127093626075/1152921504606846976 : ℚ),(1272366127093626093/1152921504606846976 : ℚ)⟩
theorem qLower1_valid : qLower1.Valid := by decide +kernel
def qUpper1 : ExpEndpointCertificate :=
  ⟨(-1276331732869287323/14411518807585587200 : ℚ),20,(579660428901589437/576460752303423488 : ℚ),(1159320857803178875/1152921504606846976 : ℚ),(1259685976006104089/1152921504606846976 : ℚ),(314921494001526027/288230376151711744 : ℚ)⟩
theorem qUpper1_valid : qUpper1.Valid := by decide +kernel
def pLower12 : ExpEndpointCertificate :=
  ⟨(-142067454738265747/1441151880758558720 : ℚ),20,(1160046804981862739/1152921504606846976 : ℚ),(290011701245465685/288230376151711744 : ℚ),(1272366127093626075/1152921504606846976 : ℚ),(1272366127093626093/1152921504606846976 : ℚ)⟩
theorem pLower12_valid : pLower12.Valid := by decide +kernel
def pUpper12 : ExpEndpointCertificate :=
  ⟨(-1276331732869287323/14411518807585587200 : ℚ),20,(579660428901589437/576460752303423488 : ℚ),(1159320857803178875/1152921504606846976 : ℚ),(1259685976006104089/1152921504606846976 : ℚ),(314921494001526027/288230376151711744 : ℚ)⟩
theorem pUpper12_valid : pUpper12.Valid := by decide +kernel
def qLower2 : ExpEndpointCertificate :=
  ⟨(-142067454738265747/1441151880758558720 : ℚ),20,(1160046804981862739/1152921504606846976 : ℚ),(290011701245465685/288230376151711744 : ℚ),(1272366127093626075/1152921504606846976 : ℚ),(1272366127093626093/1152921504606846976 : ℚ)⟩
theorem qLower2_valid : qLower2.Valid := by decide +kernel
def qUpper2 : ExpEndpointCertificate :=
  ⟨(-1276331732869287323/14411518807585587200 : ℚ),20,(579660428901589437/576460752303423488 : ℚ),(1159320857803178875/1152921504606846976 : ℚ),(1259685976006104089/1152921504606846976 : ℚ),(314921494001526027/288230376151711744 : ℚ)⟩
theorem qUpper2_valid : qUpper2.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨1638186670072100,1656396785073242⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def box : FamilyBoxCertificate :=
  ⟨parameter,![⟨-412722149775601,-407255175153669⟩,⟨772609239822009,783110450995043⟩,⟨5053208703251,5110261473118⟩,⟨-38332264150859,-37853608673014⟩,⟨7104650257815852,7120885758133249⟩,⟨-730496135930059,-720636759669589⟩,⟨135254532390937106,135702381425838031⟩],
    ![qLower0,qLower1,qLower2],![qUpper0,qUpper1,qUpper2]⟩
theorem box_valid : box.Valid := by
  refine ⟨parameter_valid,?_,?_,?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact qLower0_valid
    · exact qLower1_valid
    · exact qLower2_valid
  · intro i; fin_cases i
    · exact qUpper0_valid
    · exact qUpper1_valid
    · exact qUpper2_valid
def pairLower : Fin 3 → Fin 3 → ExpEndpointCertificate :=
  ![![qLower0,pLower01,pLower02],![pLower01,qLower1,pLower12],![pLower02,pLower12,qLower2]]
def pairUpper : Fin 3 → Fin 3 → ExpEndpointCertificate :=
  ![![qUpper0,pUpper01,pUpper02],![pUpper01,qUpper1,pUpper12],![pUpper02,pUpper12,qUpper2]]
def certificate : FamilyScaledBoxCertificate := ⟨box,pairLower,pairUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨box_valid,?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | skip
  · exact ⟨pLower01_valid,pUpper01_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower02_valid,pUpper02_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower01_valid,pUpper01_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower12_valid,pUpper12_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower02_valid,pUpper02_valid,by decide +kernel,by decide +kernel⟩
  · exact ⟨pLower12_valid,pUpper12_valid,by decide +kernel,by decide +kernel⟩
def transform : FamilyRationalMatrix := ![![(350573/250000 : ℚ),(-25737/1000000 : ℚ),(-337/12500 : ℚ)],![(0/1 : ℚ),(4123407/500000 : ℚ),(95763/250000 : ℚ)],![(0/1 : ℚ),(0/1 : ℚ),(4127853/500000 : ℚ)]]
theorem margins_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.hessianIntervals transform) := by decide +kernel
theorem hessian_positive {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (parameter.logLower.q : ℝ) (parameter.logUpper.q : ℝ))
    {q : FamilyVector}
    (hq : ∀i,Bounds (q i) ((box.qLower i).q : ℝ) ((box.qUpper i).q : ℝ))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  certificate.hessian_positive certificate_valid transform margins_checked hz hL hq hv
def offsetBox : ReplayBox 4 := ⟨![(949/100 : ℚ), (-1/10 : ℚ), (-1/10 : ℚ), (-1/10 : ℚ)],![(19/2 : ℚ), (-9/100 : ℚ), (-9/100 : ℚ), (-9/100 : ℚ)]⟩
theorem encloses_offsets : box.EnclosesABBOffsets offsetBox := by decide +kernel
theorem offset_hessian_positive {z : ℝ} (hz : 0<z) (hz1 : z<1)
    {q : FamilyVector} (hq : offsetBox.Contains (familyABBOffsetCoordinates z q))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=
  certificate.abb_offset_hessian_positive certificate_valid transform margins_checked
    encloses_offsets hz hz1 hq hv
end Leaf1

end SparseLowerTail.Certificate.FamilyScaledSmoke
