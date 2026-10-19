import SparseLowerTail.Section08.FamilyLocalFactoredIntervals
import SparseLowerTail.Section08.FamilyLocalContacts

/-! Full-parameter local AAA certificate, with exact interval arithmetic.
No numerical success flags or external certificate hypotheses are used. -/
namespace SparseLowerTail.Certificate.FamilyAAACover
open Numerics Section04
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Leaf0
def logLower : ExpEndpointCertificate := ⟨(39/10 : ℚ),20,(903525595301201735/1152921504606846976 : ℚ),(112940699412650217/144115188075855872 : ℚ),(2917166875026919/144115188075855872 : ℚ),(11668667500107677/576460752303423488 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate := ⟨(17/4 : ℚ),20,(883975580764056093/1152921504606846976 : ℚ),(441987790382028047/576460752303423488 : ℚ),(16445542020427427/1152921504606846976 : ℚ),(4111385505106857/288230376151711744 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate := ⟨(132014539518452483/1152921504606846976 : ℚ),20,(1144700049490331395/1152921504606846976 : ℚ),(286175012372582849/288230376151711744 : ℚ),(514092339261817671/576460752303423488 : ℚ),(514092339261817679/576460752303423488 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate := ⟨(206648601734771603/1152921504606846976 : ℚ),20,(1140078040402515237/1152921504606846976 : ℚ),(570039020201257619/576460752303423488 : ℚ),(240933506121779249/288230376151711744 : ℚ),(481867012243558505/576460752303423488 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate := ⟨(489313/125000 : ℚ),20,(902706920469490309/1152921504606846976 : ℚ),(451353460234745155/576460752303423488 : ℚ),(23001293159760485/1152921504606846976 : ℚ),(11500646579880243/576460752303423488 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate := ⟨(113231/25000 : ℚ),20,(868681842118665609/1152921504606846976 : ℚ),(434340921059332805/576460752303423488 : ℚ),(12147190543595/1125899906842624 : ℚ),(12438723116641281/1152921504606846976 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨132014539518452483,206648601734771603⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def certificate : FamilyBoxCertificate :=
  ⟨parameter,![⟨-39375891899607521,-16357098947696040⟩,⟨33552541332756329,77715102205965103⟩,⟨1350613621836849,2712850572713988⟩,⟨-6639202166948291,-2708454868935785⟩,⟨20961786744651727,32921503689256240⟩,⟨-73918701246778423,-31115749930704413⟩,⟨240816903367349997,366537233632608420⟩],fun _ => qLower,fun _ => qUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩
  intro i; fin_cases i <;> decide +kernel
def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0
theorem hessian_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel
theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10 : ℚ) (17/4 : ℚ)) : z≤1/40 := by
  have h := parameter.zInterval_contains parameter_valid hz hL
  apply h.2.trans
  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,
    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10 : ℚ) (17/4 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    ∀i,Bounds (q i) (489313/125000 : ℚ) (113231/25000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤(1/10:ℝ) at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10 : ℚ) (17/4 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end Leaf0

namespace Leaf1
def logLower : ExpEndpointCertificate := ⟨(17/4 : ℚ),20,(883975580764056093/1152921504606846976 : ℚ),(441987790382028047/576460752303423488 : ℚ),(16445542020427427/1152921504606846976 : ℚ),(4111385505106857/288230376151711744 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate := ⟨(23/5 : ℚ),20,(864848579222214911/1152921504606846976 : ℚ),(3378314762586777/4503599627370496 : ℚ),(5794488795381917/576460752303423488 : ℚ),(2897244397690959/288230376151711744 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate := ⟨(100516912337544961/1152921504606846976 : ℚ),20,(573328141393682723/576460752303423488 : ℚ),(1146656282787365447/1152921504606846976 : ℚ),(528330869562506545/576460752303423488 : ℚ),(528330869562506553/576460752303423488 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate := ⟨(155709456867918325/1152921504606846976 : ℚ),20,(1143230621593407025/1152921504606846976 : ℚ),(571615310796703513/576460752303423488 : ℚ),(1007269026612851357/1152921504606846976 : ℚ),(251817256653212843/288230376151711744 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate := ⟨(66206/15625 : ℚ),20,(221170982214946843/288230376151711744 : ℚ),(884683928859787373/1152921504606846976 : ℚ),(8328832232082621/576460752303423488 : ℚ),(16657664464165243/1152921504606846976 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate := ⟨(4835057/1000000 : ℚ),20,(13316186067280437/18014398509481984 : ℚ),(852235908305947969/1152921504606846976 : ℚ),(9161385646393743/1152921504606846976 : ℚ),(572586602899609/72057594037927936 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨100516912337544961,155709456867918325⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def certificate : FamilyBoxCertificate :=
  ⟨parameter,![⟨-32125968467975032,-14644702258372977⟩,⟨29154246782478240,62452111491140637⟩,⟨1009378041366862,1877516808848373⟩,⟨-5158895614332308,-2346845600762925⟩,⟨20913203127664478,30048839139848530⟩,⟨-58150178696211740,-26667791751614571⟩,⟨237641941884232923,338705315289087197⟩],fun _ => qLower,fun _ => qUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩
  intro i; fin_cases i <;> decide +kernel
def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0
theorem hessian_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel
theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (17/4 : ℚ) (23/5 : ℚ)) : z≤1/40 := by
  have h := parameter.zInterval_contains parameter_valid hz hL
  apply h.2.trans
  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,
    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (17/4 : ℚ) (23/5 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    ∀i,Bounds (q i) (66206/15625 : ℚ) (4835057/1000000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤(1/10:ℝ) at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (17/4 : ℚ) (23/5 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end Leaf1

namespace Leaf2
def logLower : ExpEndpointCertificate := ⟨(23/5 : ℚ),20,(864848579222214911/1152921504606846976 : ℚ),(3378314762586777/4503599627370496 : ℚ),(5794488795381917/576460752303423488 : ℚ),(2897244397690959/288230376151711744 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate := ⟨(53/10 : ℚ),20,(206956800358638637/288230376151711744 : ℚ),(827827201434554549/1152921504606846976 : ℚ),(359682247346331/72057594037927936 : ℚ),(5754915957541297/1152921504606846976 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate := ⟨(26738886504237847/576460752303423488 : ℚ),20,(574791991963706963/576460752303423488 : ℚ),(1149583983927413927/1152921504606846976 : ℚ),(550332523647035735/576460752303423488 : ℚ),(550332523647035743/576460752303423488 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate := ⟨(125350502444467857/1152921504606846976 : ℚ),20,(286278414111135863/288230376151711744 : ℚ),(1145113656444543453/1152921504606846976 : ℚ),(1034144929350309509/1152921504606846976 : ℚ),(258536232337577381/288230376151711744 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate := ⟨(284149/62500 : ℚ),20,(867751548018906241/1152921504606846976 : ℚ),(433875774009453121/576460752303423488 : ℚ),(6113645610166883/576460752303423488 : ℚ),(12227291220333767/1152921504606846976 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate := ⟨(220349/40000 : ℚ),20,(408549035739536973/576460752303423488 : ℚ),(817098071479073947/1152921504606846976 : ℚ),(291924730105715/72057594037927936 : ℚ),(4670795681691441/1152921504606846976 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨53477773008475694,125350502444467857⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def certificate : FamilyBoxCertificate :=
  ⟨parameter,![⟨-31777475650182184,-7959020395524264⟩,⟨15551898717129535,60717209480687208⟩,⟨462671179362629,1377713471222361⟩,⟨-4722650635588725,-1215176363531571⟩,⟨16968309567589844,29352612443835660⟩,⟨-56047455965885827,-14034931818620208⟩,⟨195979015890541626,348350826765001427⟩],fun _ => qLower,fun _ => qUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩
  intro i; fin_cases i <;> decide +kernel
def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0
theorem hessian_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel
theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (23/5 : ℚ) (53/10 : ℚ)) : z≤1/40 := by
  have h := parameter.zInterval_contains parameter_valid hz hL
  apply h.2.trans
  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,
    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (23/5 : ℚ) (53/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    ∀i,Bounds (q i) (284149/62500 : ℚ) (220349/40000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤(1/10:ℝ) at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (23/5 : ℚ) (53/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end Leaf2

namespace Leaf3
def logLower : ExpEndpointCertificate := ⟨(53/10 : ℚ),20,(206956800358638637/288230376151711744 : ℚ),(827827201434554549/1152921504606846976 : ℚ),(359682247346331/72057594037927936 : ℚ),(5754915957541297/1152921504606846976 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate := ⟨(67/10 : ℚ),20,(758470904420271347/1152921504606846976 : ℚ),(189617726105067837/288230376151711744 : ℚ),(709572401434393/576460752303423488 : ℚ),(1419144802868787/1152921504606846976 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate := ⟨(15080036454710391/1152921504606846976 : ℚ),20,(1151979387466760479/1152921504606846976 : ℚ),(35999355858336265/36028797018963968 : ℚ),(1137939661848391817/1152921504606846976 : ℚ),(568969830924195917/576460752303423488 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate := ⟨(77891538947127657/1152921504606846976 : ℚ),20,(1148063547024883745/1152921504606846976 : ℚ),(574031773512441873/576460752303423488 : ℚ),(538801440211149685/576460752303423488 : ℚ),(538801440211149693/576460752303423488 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate := ⟨(5213079/1000000 : ℚ),20,(832336662319057703/1152921504606846976 : ℚ),(104042082789882213/144115188075855872 : ℚ),(6277522766251473/1152921504606846976 : ℚ),(3138761383125737/576460752303423488 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate := ⟨(6867561/1000000 : ℚ),20,(93821152267340001/144115188075855872 : ℚ),(750569218138720009/1152921504606846976 : ℚ),(300051568999385/288230376151711744 : ℚ),(1200206275997541/1152921504606846976 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨15080036454710391,77891538947127657⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def certificate : FamilyBoxCertificate :=
  ⟨parameter,![⟨-24331289900918942,-2338412378291018⟩,⟨4436638429065510,46271287927780219⟩,⟨99620642969464,641295628829943⟩,⟨-3071063540799389,-327968861262895⟩,⟨11899771904118880,24151221422911727⟩,⟨-42667884554754929,-3989241099659640⟩,⟨144742580053763056,335545492250183238⟩],fun _ => qLower,fun _ => qUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩
  intro i; fin_cases i <;> decide +kernel
def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0
theorem hessian_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel
theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (53/10 : ℚ) (67/10 : ℚ)) : z≤1/40 := by
  have h := parameter.zInterval_contains parameter_valid hz hL
  apply h.2.trans
  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,
    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (53/10 : ℚ) (67/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    ∀i,Bounds (q i) (5213079/1000000 : ℚ) (6867561/1000000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤(1/10:ℝ) at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (53/10 : ℚ) (67/10 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end Leaf3

namespace Leaf4
def logLower : ExpEndpointCertificate := ⟨(67/10 : ℚ),20,(758470904420271347/1152921504606846976 : ℚ),(189617726105067837/288230376151711744 : ℚ),(709572401434393/576460752303423488 : ℚ),(1419144802868787/1152921504606846976 : ℚ)⟩
theorem logLower_valid : logLower.Valid := by decide +kernel
def logUpper : ExpEndpointCertificate := ⟨(19/2 : ℚ),20,(636703725764767213/1152921504606846976 : ℚ),(318351862882383607/576460752303423488 : ℚ),(86298284336703/1152921504606846976 : ℚ),(1348410692761/18014398509481984 : ℚ)⟩
theorem logUpper_valid : logUpper.Valid := by decide +kernel
def deltaLower : ExpEndpointCertificate := ⟨(578285073207749/576460752303423488 : ℚ),20,(1152849221238723521/1152921504606846976 : ℚ),(576424610619361761/576460752303423488 : ℚ),(143970689297707993/144115188075855872 : ℚ),(1151765514381663961/1152921504606846976 : ℚ)⟩
theorem deltaLower_valid : deltaLower.Valid := by decide +kernel
def deltaUpper : ExpEndpointCertificate := ⟨(27030254022594119/1152921504606846976 : ℚ),20,(1151233350869308145/1152921504606846976 : ℚ),(575616675434654073/576460752303423488 : ℚ),(1126205651013473669/1152921504606846976 : ℚ),(563102825506736843/576460752303423488 : ℚ)⟩
theorem deltaUpper_valid : deltaUpper.Valid := by decide +kernel
def qLower : ExpEndpointCertificate := ⟨(6601003/1000000 : ℚ),20,(763178349125960939/1152921504606846976 : ℚ),(190794587281490235/288230376151711744 : ℚ),(1566825250558757/1152921504606846976 : ℚ),(783412625279379/576460752303423488 : ℚ)⟩
theorem qLower_valid : qLower.Valid := by decide +kernel
def qUpper : ExpEndpointCertificate := ⟨(4811723/500000 : ℚ),20,(157952554912148961/288230376151711744 : ℚ),(631810219648595845/1152921504606846976 : ℚ),(38138205056975/576460752303423488 : ℚ),(76276410113951/1152921504606846976 : ℚ)⟩
theorem qUpper_valid : qUpper.Valid := by decide +kernel
def parameter : FamilyParameterCertificate :=
  ⟨logLower,logUpper,deltaLower,deltaUpper,⟨1156570146415498,27030254022594119⟩⟩
theorem parameter_valid : parameter.Valid := by
  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩
  all_goals decide +kernel
def certificate : FamilyBoxCertificate :=
  ⟨parameter,![⟨-9873178503525150,-184806012592639⟩,⟨341354426858975,19034602738201733⟩,⟨4710369129047,124095838689020⟩,⟨-934932933131759,-22096267776835⟩,⟨6599709966327489,15043812785385814⟩,⟨-17843301420039978,-310350761897923⟩,⟨92695519308574677,287112878928247907⟩],fun _ => qLower,fun _ => qUpper⟩
theorem certificate_valid : certificate.Valid := by
  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩
  intro i; fin_cases i <;> decide +kernel
def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0
theorem hessian_checked : FamilyIntervalPositive
    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel
theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (67/10 : ℚ) (19/2 : ℚ)) : z≤1/40 := by
  have h := parameter.zInterval_contains parameter_valid hz hL
  apply h.2.trans
  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,
    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]
theorem cube_in_box {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (67/10 : ℚ) (19/2 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    ∀i,Bounds (q i) (6601003/1000000 : ℚ) (4811723/500000 : ℚ) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  have hd := parameter.delta_contains parameter_valid hz hL
  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd
  intro i
  have hqi := hq i
  change |q i-qA z|≤(1/10:ℝ) at hqi
  rw [qA_eq_add hz hz1] at hqi
  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring
  rw [he] at hqi
  have hh := abs_le.mp hqi
  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]
theorem hessian_positive {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (67/10 : ℚ) (19/2 : ℚ))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv
end Leaf4

theorem parameter_covered {L : ℝ} (hL : Bounds L (39/10) (19/2)) :
    Bounds L (39/10 : ℚ) (17/4 : ℚ) ∨
    Bounds L (17/4 : ℚ) (23/5 : ℚ) ∨
    Bounds L (23/5 : ℚ) (53/10 : ℚ) ∨
    Bounds L (53/10 : ℚ) (67/10 : ℚ) ∨
    Bounds L (67/10 : ℚ) (19/2 : ℚ) := by
  rcases hL with ⟨hl,hu⟩
  norm_num only [Bounds, Rat.cast_div, Rat.cast_ofNat]
  by_cases h0 : L≤17/4
  · exact Or.inl ⟨hl,h0⟩
  by_cases h1 : L≤23/5
  · exact Or.inr (Or.inl ⟨by linarith,h1⟩)
  by_cases h2 : L≤53/10
  · exact Or.inr (Or.inr (Or.inl ⟨by linarith,h2⟩))
  by_cases h3 : L≤67/10
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith,h3⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith,hu⟩)))

theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2)) : z≤1/40 := by
  rcases parameter_covered hL with h | h | h | h | h
  · exact Leaf0.z_le_one_fortieth hz h
  · exact Leaf1.z_le_one_fortieth hz h
  · exact Leaf2.z_le_one_fortieth hz h
  · exact Leaf3.z_le_one_fortieth hz h
  · exact Leaf4.z_le_one_fortieth hz h

theorem hessian_positive {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))
    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by
  rcases parameter_covered hL with h | h | h | h | h
  · exact Leaf0.hessian_positive hz h hq hv
  · exact Leaf1.hessian_positive hz h hq hv
  · exact Leaf2.hessian_positive hz h hq hv
  · exact Leaf3.hessian_positive hz h hq hv
  · exact Leaf4.hessian_positive hz h hq hv

/-- Full local AAA result over the complete compact parameter range. -/
theorem local_nonnegative_and_unique_zero {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactAAA z) := by
  have hz40 := z_le_one_fortieth hz hL
  have hz1 : z<1 := by linarith
  exact familyContactAAA_local hz hz1 (gamma_branch_neg hz hz40).ne (by norm_num)
    (fun _ hq _ hv => hessian_positive hz hL hq hv) hq

end SparseLowerTail.Certificate.FamilyAAACover
