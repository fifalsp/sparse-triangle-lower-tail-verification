#!/usr/bin/env python3
"""Propose refined apex primitive bounds; all analytic steps compile in Lean."""
from pathlib import Path
from fractions import Fraction as F
import json
from generate_refined_threshold_digits import main as refined
ROOT=Path(__file__).resolve().parents[1]
def main():
 env=refined();env['lines'].clear();Node=env['Node'];Node.i=0;emit=env['emit'];q=env['q']
 a=env['tightA'];b=env['tightB'];mu=env['tightMu'];E=env['E']
 L=Node('(branchLog transitionParameter)',env['Ll'],env['Lu'],'hL')
 QB=Node('(2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2)',E.lo,E.hi,'hE')
 QA=L+QB
 calc_log=list(env['lines']);env['lines'].clear()
 A=Node('criticalA',a.lo,a.hi,'hA');B=Node('criticalB',b.lo,b.hi,'hB')
 QA=Node('(-Real.log criticalA)',QA.lo,QA.hi,'hQA');QB=Node('(-Real.log criticalB)',QB.lo,QB.hi,'hQB')
 one=Node.c(1);two=Node.c(2);three=Node.c(3);four=Node.c(4)
 HA=one-A*(QA+one);HB=one-B*(QB+one)
 tri=(A*A*A+three*A*(B*B))/four
 omega=(B-A)/(HA-HB)
 mean=(A+B)/two;cost=(HA+HB)/two
 calculated=list(env['lines'])
 values=[QA,QB,A,B,tri,omega,mu,mean,cost]
 def qr(x):return f'({x.numerator}/{x.denominator} : ℚ)'
 intervals='!['+','.join(f'⟨{qr(v.lo)},{qr(v.hi)}⟩'for v in values)+']'
 s=['import SparseLowerTail.Section04.RefinedThresholdDigits','import SparseLowerTail.Section05.ApexTangencyExpressions','',
 '/-! Refined bounds derived from the actual crossing, not assumed decimal constants. -/',
 'noncomputable section','namespace SparseLowerTail.Section05','open Numerics Section04','',
 f'def apexRefinedPrimitiveBounds : Fin 9 → RationalInterval := {intervals}','',
 'theorem apexRefinedPrimitiveBounds_contains (i : Fin 9) :',
 '    (apexRefinedPrimitiveBounds i).contains (apexPrimitiveValues i) := by',
 '  have hz : transitionParameter∈Set.Icc Refined.digitZLower Refined.digitZUpper :=',
 '    ⟨Refined.transitionParameter_digits.1.le,Refined.transitionParameter_digits.2.le⟩',
 '  have hp := Refined.tight_branch_ranges hz',
 f'  have hA : Bounds criticalA {q(a.lo)} {q(a.hi)} := hp.1',
 f'  have hB : Bounds criticalB {q(b.lo)} {q(b.hi)} := hp.2.1',
 '  have hL := Refined.digit_log_range hz','  have hE := Refined.digit_exponent_range hz',
 '  have hqa : -Real.log criticalA=branchLog transitionParameter+',
 '      2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2 := by',
 '    rw [criticalA,branchA,Real.log_mul (ne_of_gt transitionParameter_mem_Ioo.1)',
 '      (ne_of_gt (branchB_pos _)),log_branchB,branchLog_eq_neg_log]','    ring',
 '  have hqb : -Real.log criticalB=2*transitionParameter*branchLog transitionParameter/(1-transitionParameter)^2 := by',
 '    rw [criticalB,log_branchB]','    ring']
 s+=calc_log
 s +=[f'  have hQA : Bounds (-Real.log criticalA) {q(QA.lo)} {q(QA.hi)} := by',
 '    rw [hqa]','    exact h1',
 f'  have hQB : Bounds (-Real.log criticalB) {q(QB.lo)} {q(QB.hi)} := by',
 '    rw [hqb]','    exact hE']
 s+=calculated
 # Give semantic names to the interval computations before resolving all nine coordinates.
 for name,node,expr,proof in [
  ('ht',tri,'criticalTriangle','rw [←critical_pair_triangle]\n    norm_num [balancedTriangle,pow_succ,pow_two]\n    ring'),
  ('ho',omega,'criticalOmega','unfold criticalOmega entropy\n    ring'),
  ('hm',mean,'criticalMean','rfl'),
  ('hf',cost,'criticalCost','rw [←critical_pair_cost]\n    unfold balancedCost entropy\n    ring')]:
  s +=[f'  have {name} : Bounds {expr} {q(node.lo)} {q(node.hi)} := by',
   f'    convert {node.h} using 1']
  if name=='ht':s+=['    change criticalTriangle='+node.e,'    rw [show criticalTriangle=balancedTriangle criticalA criticalB from critical_pair_triangle.symm]', '    unfold balancedTriangle','    ring']
  elif name=='ho':s+=['    unfold criticalOmega entropy','    ring']
  elif name=='hm':pass
  else:s+=['    rw [show criticalCost=balancedCost criticalA criticalB from critical_pair_cost.symm]', '    unfold balancedCost entropy','    ring']
 s +=[f'  have hmu : Bounds (relaxationMultiplier criticalPoint) {q(mu.lo)} {q(mu.hi)} := by',
 '    rw [criticalMultiplier_eq_branchMu]','    exact hp.2.2','  fin_cases i']
 for name in ['hQA','hQB','hA','hB','ht','ho','hmu','hm','hf']:
  s +=[f'  · norm_num [apexRefinedPrimitiveBounds,RationalInterval.contains,apexPrimitiveValues] at ⊢',f'    exact {name}']
 s +=['','def apexRefinedPrimitiveIntervals (i : Fin 9) : DyadicInterval :=', '  DyadicInterval.ofRational (apexRefinedPrimitiveBounds i)', '', 'theorem apexRefinedPrimitiveIntervals_contains (i : Fin 9) :', '    (apexRefinedPrimitiveIntervals i).contains (apexPrimitiveValues i) :=', '  DyadicInterval.ofRational_contains (apexRefinedPrimitiveBounds_contains i)', '', 'end SparseLowerTail.Section05','']
 (ROOT/'SparseLowerTail/Section05/ApexRefinedPrimitives.lean').write_text('\n'.join(s))
 (ROOT/'data/apex-refined-primitive-proposal.json').write_text(json.dumps({'trust_status':'proposal only; theorem apexRefinedPrimitiveBounds_contains must compile','bounds':[[str(v.lo),str(v.hi)]for v in values]},indent=2)+'\n')
 for name,v in zip(['qa','qb','a','b','triangle','omega','mu','mean','cost'],values):print(name,'width',float(v.hi-v.lo))
if __name__=='__main__':main()
