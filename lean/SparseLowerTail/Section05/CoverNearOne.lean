import SparseLowerTail.Section05.CoverJobIntervals

/-! One endpoint box, all thirty-six actual nonapex jobs. -/
namespace SparseLowerTail.Section05.CoverNearOne
open Numerics Certificate CoverGeometry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def lower : ExpEndpointCertificate := ⟨(0/1 : ℚ),20,(1/1 : ℚ),(1/1 : ℚ),(1/1 : ℚ),(1/1 : ℚ)⟩
theorem lower_valid : lower.Valid := by decide +kernel
def upper : ExpEndpointCertificate := ⟨(1/512 : ℚ),20,(1152780775708076725/1152921504606846976 : ℚ),(576390387854038363/576460752303423488 : ℚ),(1150671902385460287/1152921504606846976 : ℚ),(71916993899091269/72057594037927936 : ℚ)⟩
theorem upper_valid : upper.Valid := by decide +kernel

def box : ApexFanBox := ⟨fun _ => lower,fun _ => upper⟩
theorem box_valid : box.Valid := ⟨fun _ => lower_valid,fun _ => upper_valid⟩

theorem all_jobs_checked (j : Fin 36) :
    0<(apexCertificateExpr.dyadicEval (nonapexBoxIntervals box j)).lower := by
  fin_cases j <;> decide +kernel

theorem all_jobs_positive (j : Fin 36) {q : ApexVector}
    (hq : ∀i,Bounds (q i) 0 (1/512)) :
    0<coverPhi (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j)) (nonapexVertex j) q := by
  apply nonapexBox_positive box box_valid j (all_jobs_checked j)
  intro i
  simpa [box,lower,upper] using hq i

end SparseLowerTail.Section05.CoverNearOne
