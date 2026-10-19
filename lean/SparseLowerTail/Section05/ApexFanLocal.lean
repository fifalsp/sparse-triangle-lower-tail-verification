import SparseLowerTail.Section05.ApexLocalReplay.F1AAA
import SparseLowerTail.Section05.ApexLocalReplay.F1ABB
import SparseLowerTail.Section05.ApexLocalReplay.F2AAA
import SparseLowerTail.Section05.ApexLocalReplay.F2ABB
import SparseLowerTail.Section05.ApexLocalReplay.F3AAA
import SparseLowerTail.Section05.ApexLocalReplay.F3ABB
import SparseLowerTail.Section05.ApexLocalReplay.F4AAA
import SparseLowerTail.Section05.ApexLocalReplay.F4ABB
import SparseLowerTail.Section05.ApexLocalReplay.F5AAA
import SparseLowerTail.Section05.ApexLocalReplay.F5ABB
import SparseLowerTail.Section05.ApexLocalReplay.F6AAA
import SparseLowerTail.Section05.ApexLocalReplay.F6ABB

/-! All twelve apex contact neighborhoods, at the published radii. -/
namespace SparseLowerTail.Section05
open Certificate CoverGeometry

def apexFanLocalRadius (i : Fin 6) (mixed : Bool) : ℚ :=
  if mixed then ![(1152921504606847/2305843009213693952 : ℚ),(1152921504606847/4611686018427387904 : ℚ),(1152921504606847/1152921504606846976 : ℚ),(1152921504606847/2305843009213693952 : ℚ),(1152921504606847/1152921504606846976 : ℚ),(1152921504606847/576460752303423488 : ℚ)] i
  else (1080863910568919/36028797018963968 : ℚ)

noncomputable def apexFanContact (mixed : Bool) : ApexVector :=
  if mixed then apexContactABB else apexContactAAA

theorem apexFan_local_nonneg_zero_iff (i : Fin 6) (mixed : Bool) {q : ApexVector}
    (hq : q∈familyCube (apexFanContact mixed) (apexFanLocalRadius i mixed : ℝ)) :
    0≤apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) q ∧
    (apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) q=0 ↔ q=apexFanContact mixed) := by
  fin_cases i <;> cases mixed
  · exact ApexLocalReplay.F1AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F1ABB.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F2AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F2ABB.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F3AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F3ABB.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F4AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F4ABB.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F5AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F5ABB.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F6AAA.local_nonneg_zero_iff hq
  · exact ApexLocalReplay.F6ABB.local_nonneg_zero_iff hq

end SparseLowerTail.Section05
