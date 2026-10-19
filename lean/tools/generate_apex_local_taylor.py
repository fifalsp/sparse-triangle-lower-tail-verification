#!/usr/bin/env python3
"""Generate twelve proposed full-radius local certificates, checked by Lean.
Python selects rational transformations; it is outside the trusted proof.
Run propose_apex_local_boxes.py first to refresh the input proposals.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from generate_exp_endpoints import endpoint,rat
ROOT=Path(__file__).resolve().parents[1]
BOUNDS=[(F(407254281156,10**11),F(407254281216,10**11)),(F(16328752549,10**11),F(16328752562,10**11))]
def main():
 rows=json.loads((ROOT/'data/apex-local-box-proposal.json').read_text())['boxes']
 cells=json.loads((ROOT.parent/'data/cover.json').read_text())['cells']
 if [(r['fan'],r['mixed'])for r in rows]!=[(i,b)for i in range(6)for b in [False,True]]:
  raise ValueError('Expected both contacts of all six fans in canonical order')
 for row in rows:
  published=F(cells['F'+str(row['fan']+1)]['local_radii'][int(row['mixed'])])
  if F(row['radius'])!=published:raise ValueError('Proposal radius differs from the published radius')
 target=ROOT/'SparseLowerTail/Section05/ApexLocalReplay';target.mkdir(exist_ok=True)
 for row in rows:
  fan=row['fan'];mixed=row['mixed'];pattern='ABB'if mixed else'AAA';name=f'F{fan+1}{pattern}'
  radius=F(row['radius']);ell=F(row['eigen_lower_proposal']);point='apexContact'+pattern
  center=[BOUNDS[0],BOUNDS[int(mixed)],BOUNDS[int(mixed)]]
  coords=[0,int(mixed),int(mixed)]
  lines=['import SparseLowerTail.Section05.ApexFanBoxIntervals','import SparseLowerTail.Section05.ApexTaylorIntervals','',
   '/-! Full published contact radius. Every numerical assertion is kernel checked. -/',
   f'namespace SparseLowerTail.Section05.ApexLocalReplay.{name}',
   'open Numerics Certificate CoverGeometry',
   'set_option maxRecDepth 1000000','set_option maxHeartbeats 16000000','']
  for kind,delta in [('center',F(0)),('cube',radius)]:
   endpoints={}
   for j,(a,b)in enumerate(center):
    for side,q in [('Lo',a-delta),('Hi',b+delta)]:
     key=(side,q)
     if key not in endpoints:
      label=f'{kind}{side}{j}';endpoints[key]=label
      qq,n,l,u,L,U=endpoint(q,20,60)
      lines +=[f'def {label} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(L)},{rat(U)}⟩',
       f'theorem {label}_valid : {label}.Valid := by decide +kernel']
   los=[endpoints[('Lo',a-delta)]for a,b in center];his=[endpoints[('Hi',b+delta)]for a,b in center]
   lines +=[f'def {kind} : ApexFanBox := ⟨![{",".join(los)}],![{",".join(his)}]⟩',
    f'theorem {kind}_valid : {kind}.Valid := by',
    '  constructor <;> intro j <;> fin_cases j']
   for label in los+his:lines +=[f'  · exact {label}_valid']
   lines+=['']
  lines +=[f'def radius : ℚ := {rat(radius)}',f'def ell : ℚ := {rat(ell)}',
   'def transform : FamilyRationalMatrix := !['+','.join('!['+','.join(rat(F(x))for x in r)+']'for r in row['shifted_transform'])+']','',
   'theorem hessian_checked : FamilyIntervalPositive (familyIntervalCongruence',
   f'    (apexShiftedHessianInterval (apexHessianInterval (center.variableIntervals {fan})) ell) transform) := by',
   '  decide +kernel','',
   'theorem margin_checked : radius*((∑i,∑j,∑k,',
   f'    apexThirdIntervalBound (cube.variableIntervals {fan}) i j k : ℤ) : ℚ)/',
   '    (DyadicInterval.scale : ℚ)<3*ell := by','  decide +kernel','',
   'theorem center_contains : ∀k,',f'    (center.variableIntervals {fan} k).contains',
   f'      (apexVariables (apexFanTheta {fan}) (cellLambda (({fan} : Fin 6).castAdd 6)) {point} k) := by',
   f'  apply center.variableIntervals_contains center_valid {fan}',
   '  intro j','  fin_cases j']
  for j,ix in enumerate(coords):
   labels=['centerLo0','centerHi0']+(['centerLo1','centerHi1']if mixed else[])
   lines +=[f'  · have hc := apexPrimitiveBounds_contains {ix}', '    norm_num [center,'+','.join(labels)+',apexPrimitiveBounds,apexPrimitiveValues,'+point+',RationalInterval.contains] at hc ⊢', '    exact hc']
  lines +=['','theorem cube_contains {q : ApexVector}',f'    (hq : q∈familyCube {point} (radius : ℝ)) : ∀k,',
   f'    (cube.variableIntervals {fan} k).contains',
   f'      (apexVariables (apexFanTheta {fan}) (cellLambda (({fan} : Fin 6).castAdd 6)) q k) := by',
   f'  apply cube.variableIntervals_contains cube_valid {fan}','  intro j','  fin_cases j']
  for j,ix in enumerate(coords):
   a,b=center[j]
   lines +=[f'  · have hp : Bounds ({point} {j}) ({rat(a)} : ℝ) ({rat(b)} : ℝ) := by',
    f'      have hc := apexPrimitiveBounds_contains {ix}',f'      norm_num [apexPrimitiveBounds,apexPrimitiveValues,{point},RationalInterval.contains] at hc ⊢','      exact hc',
    f'    have hd := abs_le.mp (hq {j})',
    f'    change -(radius : ℝ)≤q {j}-{point} {j} ∧ q {j}-{point} {j}≤(radius : ℝ) at hd',
    f'    change Bounds (q {j}) ({rat(a-radius)} : ℝ) ({rat(b+radius)} : ℝ)',
    '    norm_num only [radius,Rat.cast_div,Rat.cast_ofNat,Rat.cast_neg] at hp hd ⊢',
    '    constructor <;> linarith [hp.1,hp.2,hd.1,hd.2]']
  jet='.2'if mixed else'.1'
  lines +=['','/-- Positivity and the unique zero on the entire published contact cube. -/',
   f'theorem local_nonneg_zero_iff {{q : ApexVector}} (hq : q∈familyCube {point} (radius : ℝ)) :',
   f'    0≤apexPhi (apexFanTheta {fan}) (cellLambda (({fan} : Fin 6).castAdd 6)) q ∧',
   f'    (apexPhi (apexFanTheta {fan}) (cellLambda (({fan} : Fin 6).castAdd 6)) q=0 ↔ q={point}) := by',
   f'  have hj := (apexFanTheta_contacts {fan}){jet}',
   '  exact apexPhi_local_of_interval_taylor radius ell (by norm_num [radius]) (by norm_num [ell])',
   f'    hj.1 hj.2 (center.variableIntervals {fan}) (cube.variableIntervals {fan}) transform',
   '    center_contains (fun _ hr => cube_contains hr) hessian_checked margin_checked hq','',
   f'end SparseLowerTail.Section05.ApexLocalReplay.{name}','']
  (target/f'{name}.lean').write_text('\n'.join(lines))
 # A single theorem covers both contacts of every fan cell.
 names=[f'F{i+1}{p}'for i in range(6)for p in ['AAA','ABB']]
 lines=[f'import SparseLowerTail.Section05.ApexLocalReplay.{n}'for n in names]
 lines +=['','/-! All twelve apex contact neighborhoods, at the published radii. -/',
  'namespace SparseLowerTail.Section05','open Certificate CoverGeometry','',
  'def apexFanLocalRadius (i : Fin 6) (mixed : Bool) : ℚ :=',
  '  if mixed then !['+','.join(rat(F(r['radius']))for r in rows if r['mixed'])+'] i',
  '  else '+rat(F(rows[0]['radius'])),'',
  'noncomputable def apexFanContact (mixed : Bool) : ApexVector :=',
  '  if mixed then apexContactABB else apexContactAAA','',
  'theorem apexFan_local_nonneg_zero_iff (i : Fin 6) (mixed : Bool) {q : ApexVector}',
  '    (hq : q∈familyCube (apexFanContact mixed) (apexFanLocalRadius i mixed : ℝ)) :',
  '    0≤apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) q ∧',
  '    (apexPhi (apexFanTheta i) (cellLambda (i.castAdd 6)) q=0 ↔ q=apexFanContact mixed) := by',
  '  fin_cases i <;> cases mixed']
 for name in names:lines +=[f'  · exact ApexLocalReplay.{name}.local_nonneg_zero_iff hq']
 lines +=['','end SparseLowerTail.Section05','']
 (ROOT/'SparseLowerTail/Section05/ApexFanLocal.lean').write_text('\n'.join(lines))
if __name__=='__main__':main()
