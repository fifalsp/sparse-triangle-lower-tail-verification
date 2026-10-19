#!/usr/bin/env python3
"""Generate five exact local-AAA certificates. Python proposes; Lean proves.
The checked conclusion covers every L in [3.9,9.5], with radius 1/10.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from generate_family_leaf_example import I,S,ep,expbox,coeff
from generate_exp_endpoints import rat
ROOT=Path(__file__).resolve().parents[1]
rows=json.loads((ROOT/'data/family-aaa-proposal.json').read_text())['leaves']
lines=['import SparseLowerTail.Section08.FamilyLocalFactoredIntervals',
'import SparseLowerTail.Section08.FamilyLocalContacts','',
'/-! Full-parameter local AAA certificate, with exact interval arithmetic.',
'No numerical success flags or external certificate hypotheses are used. -/',
'namespace SparseLowerTail.Certificate.FamilyAAACover','open Numerics Section04',
'set_option maxRecDepth 100000','set_option maxHeartbeats 8000000','']
for k,row in enumerate(rows):
 lo,hi,ql,qh=map(F,[row['lo'],row['hi'],row['qlo'],row['qhi']]);elo,ehi=ep(lo),ep(hi)
 L=I(I(lo).l,I(hi).u);z=expbox(elo,ehi);delta=2*z*L/(1-z)**2
 dlo,dhi=ep(F(delta.l,S)),ep(F(delta.u,S));b=expbox(dlo,dhi);cs=coeff(z,L,b)
 lines +=[f'namespace Leaf{k}']
 for name,e in [('logLower',elo),('logUpper',ehi),('deltaLower',dlo),('deltaUpper',dhi),('qLower',ep(ql)),('qUpper',ep(qh))]:
  q,n,l,u,Lb,Ub=e
  lines +=[f'def {name} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(Lb)},{rat(Ub)}⟩',f'theorem {name}_valid : {name}.Valid := by decide +kernel']
 lines +=['def parameter : FamilyParameterCertificate :=',f'  ⟨logLower,logUpper,deltaLower,deltaUpper,{delta.lean()}⟩',
 'theorem parameter_valid : parameter.Valid := by',
 '  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩',
 '  all_goals decide +kernel',
 'def certificate : FamilyBoxCertificate :=',
 '  ⟨parameter,!['+','.join(c.lean()for c in cs)+'],fun _ => qLower,fun _ => qUpper⟩',
 'theorem certificate_valid : certificate.Valid := by',
 '  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩',
 '  intro i; fin_cases i <;> decide +kernel',
 'def identity : FamilyRationalMatrix := fun i j => if i=j then 1 else 0',
 'theorem hessian_checked : FamilyIntervalPositive',
 '    (familyIntervalCongruence certificate.factoredHessianIntervals identity) := by decide +kernel',
 f'theorem z_le_one_fortieth {{z : ℝ}} (hz : 0<z) (hL : Bounds (branchLog z) {rat(lo)} {rat(hi)}) : z≤1/40 := by',
 '  have h := parameter.zInterval_contains parameter_valid hz hL',
 '  apply h.2.trans',
 '  norm_num [FamilyParameterCertificate.zInterval,expEndpointInterval,parameter,logLower,logUpper,',
 '    DyadicInterval.ofRational,DyadicInterval.point,DyadicInterval.ceilDiv,DyadicInterval.scale]',
 f'theorem cube_in_box {{z : ℝ}} (hz : 0<z) (hL : Bounds (branchLog z) {rat(lo)} {rat(hi)})',
 '    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :',
 f'    ∀i,Bounds (q i) {rat(ql)} {rat(qh)} := by',
 '  have hz40 := z_le_one_fortieth hz hL',
 '  have hz1 : z<1 := by linarith',
 '  have hd := parameter.delta_contains parameter_valid hz hL',
 '  norm_num only [parameter,DyadicInterval.contains,DyadicInterval.scale,Int.cast_ofNat] at hd',
 '  intro i',
 '  have hqi := hq i',
 '  change |q i-qA z|≤(1/10:ℝ) at hqi',
 '  rw [qA_eq_add hz hz1] at hqi',
 '  have he : 2*branchLog z*z/(1-z)^2=2*z*branchLog z/(1-z)^2 := by ring',
 '  rw [he] at hqi',
 '  have hh := abs_le.mp hqi',
 '  constructor <;> linarith [hd.1,hd.2,hL.1,hL.2]',
 f'theorem hessian_positive {{z : ℝ}} (hz : 0<z) (hL : Bounds (branchLog z) {rat(lo)} {rat(hi)})',
 '    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))',
 '    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by',
 '  exact certificate.factored_hessian_positive certificate_valid identity hessian_checked hz hL (cube_in_box hz hL hq) hv',
 f'end Leaf{k}','']
lines +=['theorem parameter_covered {L : ℝ} (hL : Bounds L (39/10) (19/2)) :',
 '    '+' ∨\n    '.join(f'Bounds L {rat(F(r["lo"]))} {rat(F(r["hi"]))}'for r in rows)+' := by',
 '  rcases hL with ⟨hl,hu⟩',
 '  norm_num only [Bounds, Rat.cast_div, Rat.cast_ofNat]',
 '  by_cases h0 : L≤17/4', '  · exact Or.inl ⟨hl,h0⟩',
 '  by_cases h1 : L≤23/5','  · exact Or.inr (Or.inl ⟨by linarith,h1⟩)',
 '  by_cases h2 : L≤53/10','  · exact Or.inr (Or.inr (Or.inl ⟨by linarith,h2⟩))',
 '  by_cases h3 : L≤67/10','  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith,h3⟩)))',
 '  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith,hu⟩)))','',
 'theorem z_le_one_fortieth {z : ℝ} (hz : 0<z) (hL : Bounds (branchLog z) (39/10) (19/2)) : z≤1/40 := by',
 '  rcases parameter_covered hL with h | h | h | h | h']
for k in range(5):lines +=[f'  · exact Leaf{k}.z_le_one_fortieth hz h']
lines +=['','theorem hessian_positive {z : ℝ} (hz : 0<z)',
 '    (hL : Bounds (branchLog z) (39/10) (19/2))',
 '    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10))',
 '    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v := by',
 '  rcases parameter_covered hL with h | h | h | h | h']
for k in range(5):lines +=[f'  · exact Leaf{k}.hessian_positive hz h hq hv']
lines +=['','/-- Full local AAA result over the complete compact parameter range. -/',
 'theorem local_nonnegative_and_unique_zero {z : ℝ} (hz : 0<z)',
 '    (hL : Bounds (branchLog z) (39/10) (19/2))',
 '    {q : FamilyVector} (hq : q∈familyCube (familyContactAAA z) (1/10)) :',
 '    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactAAA z) := by',
 '  have hz40 := z_le_one_fortieth hz hL',
 '  have hz1 : z<1 := by linarith',
 '  exact familyContactAAA_local hz hz1 (gamma_branch_neg hz hz40).ne (by norm_num)',
 '    (fun _ hq _ hv => hessian_positive hz hL hq hv) hq','',
 'end SparseLowerTail.Certificate.FamilyAAACover','']
(ROOT/'SparseLowerTail/Section08/FamilyAAACover.lean').write_text('\n'.join(lines))
print('Generated five exact local-AAA leaves and their full-parameter assembly.')
