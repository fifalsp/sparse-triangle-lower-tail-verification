#!/usr/bin/env python3
"""Generate a shared near-one check for all 36 nonapex jobs.
Every interval assertion is independently checked by the Lean kernel.
"""
from pathlib import Path
from fractions import Fraction as F
from generate_exp_endpoints import endpoint,rat
ROOT=Path(__file__).resolve().parents[1]
def main():
 lines=['import SparseLowerTail.Section05.CoverJobIntervals','',
  '/-! One endpoint box, all thirty-six actual nonapex jobs. -/',
  'namespace SparseLowerTail.Section05.CoverNearOne',
  'open Numerics Certificate CoverGeometry',
  'set_option maxRecDepth 1000000','set_option maxHeartbeats 16000000','']
 for name,q in [('lower',F(0)),('upper',F(1,512))]:
  q,n,l,u,L,U=endpoint(q,20,60)
  lines +=[f'def {name} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(L)},{rat(U)}⟩',
   f'theorem {name}_valid : {name}.Valid := by decide +kernel']
 lines +=['','def box : ApexFanBox := ⟨fun _ => lower,fun _ => upper⟩',
  'theorem box_valid : box.Valid := ⟨fun _ => lower_valid,fun _ => upper_valid⟩','',
  'theorem all_jobs_checked (j : Fin 36) :',
  '    0<(apexCertificateExpr.dyadicEval (nonapexBoxIntervals box j)).lower := by',
  '  fin_cases j <;> decide +kernel','',
  'theorem all_jobs_positive (j : Fin 36) {q : ApexVector}',
  '    (hq : ∀i,Bounds (q i) 0 (1/512)) :',
  '    0<coverPhi (coverCellTheta (nonapexCell j)) (cellLambda (nonapexCell j)) (nonapexVertex j) q := by',
  '  apply nonapexBox_positive box box_valid j (all_jobs_checked j)',
  '  intro i','  simpa [box,lower,upper] using hq i','',
  'end SparseLowerTail.Section05.CoverNearOne','']
 (ROOT/'SparseLowerTail/Section05/CoverNearOne.lean').write_text('\n'.join(lines))
if __name__=='__main__':main()
