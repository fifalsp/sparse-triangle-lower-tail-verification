#!/usr/bin/env python3
"""Propose a checked coarse upper crossing bound needed by smallparams.
Run from lean/. The source generated here is checked by Lean, not trusted.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, getcontext, ROUND_FLOOR
import cover_interval_codegen as cg
getcontext().prec=70
q=cg.q;emit=cg.emit;Node=cg.Node
z=F(209,2500000);c=F(5307,20000)
def dec(x):return Decimal(x.numerator)/Decimal(x.denominator)
def bracket(x,p=12):
 d=10**p;k=int((x*d).to_integral_value(rounding=ROUND_FLOOR));return F(k-1,d),F(k+2,d)
header='''import SparseLowerTail.Section07.PenalizedCrossing
import SparseLowerTail.Numerics.IntervalArithmetic

/-! Coarse crossing bracket for lem:smallparams. Generated exact numerical
proposals are checked using proved logarithm/exponential Taylor estimates. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07
open Section04 Numerics

def smallParameterUpper : ℝ := 209/2500000
'''

def logcert(name,x,k,n):
 lo,hi=bracket(-dec(x).ln())
 emit(f'theorem {name} : Bounds (-Real.log {q(x)}) {q(lo)} {q(hi)} := by')
 emit(f'  have h := Real.abs_log_sub_add_sum_range_le (x := {q(1-2**k*x)}) (by norm_num) {n}')
 emit('  norm_num [Finset.sum_range_succ] at h')
 emit('  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2')
 emit(f'  have he : Real.log {q(2**k*x)} = {k}*Real.log 2 + Real.log {q(x)} := by')
 emit(f'    rw [show {q(2**k*x)} = (2:ℝ)^{k}*{q(x)} by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]')
 emit('    norm_num\n  rw [he] at hl hu\n  have h2l := log_two_bounds_22.1\n  have h2u := log_two_bounds_22.2\n  constructor <;> linarith\n')
 return lo,hi
Ll,Lu=logcert('smallUpper_log',z,14,40)
cl,cu=logcert('smallUpper_trial_log',c,2,14)
El,Eu=2*z*Ll/(1-z)**2,2*z*Lu/(1-z)**2
emit(f'theorem smallUpper_exponent : Bounds (2*{q(z)}*branchLog {q(z)}/(1-{q(z)})^2) {q(El)} {q(Eu)} := by')
emit('  have h := smallUpper_log\n  rw [branchLog_eq_neg_log]\n  norm_num only [sub_self,one_pow] at *\n  constructor <;> norm_num <;> nlinarith [h.1,h.2]\n')

def expcert(name,x):
 lo,hi=bracket(dec(x).exp())
 emit(f'theorem {name} : Bounds (Real.exp {q(x)}) {q(lo)} {q(hi)} := by')
 emit(f'  have h := Real.exp_bound (x := {q(x)}) (by norm_num) (n := 8) (by norm_num)')
 emit('  norm_num [Finset.sum_range_succ,Nat.factorial] at h\n  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2\n  constructor <;> linarith\n')
 return lo,hi
Bl=expcert('smallUpper_exp_lower',-Eu)[0];Bu=expcert('smallUpper_exp_upper',-El)[1]
emit(f'theorem smallUpper_branchB : Bounds (branchB {q(z)}) {q(Bl)} {q(Bu)} := by')
emit('  have hE := smallUpper_exponent\n  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)\n  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)')
emit(f'  have he : branchB {q(z)}=Real.exp (-(2*{q(z)}*branchLog {q(z)}/(1-{q(z)})^2)) := by unfold branchB; congr 1; ring')
emit('  rw [←he] at hlo hhi\n  have hbl := smallUpper_exp_lower.1\n  have hbu := smallUpper_exp_upper.2\n  constructor <;> linarith\n')
emit('theorem smallUpper_trial_gap :')
emit(f'    0< balancedPenalty (branchMu {q(z)}/3) (branchA {q(z)}) (branchB {q(z)})-constantPenalty (branchMu {q(z)}/3) {q(c)} := by')
Z=Node.c(z);C=Node.c(c);L=Node(f'(branchLog {q(z)})',Ll,Lu,'hL');B=Node(f'(branchB {q(z)})',Bl,Bu,'smallUpper_branchB');LC=Node(f'(-Real.log {q(c)})',cl,cu,'smallUpper_trial_log');one=Node.c(1);two=Node.c(2);three=Node.c(3);four=Node.c(4)
emit(f'  have hL : Bounds (branchLog {q(z)}) {q(Ll)} {q(Lu)} := by simpa only [branchLog_eq_neg_log] using smallUpper_log')
A=Z*B;M=(A+B)/two;mu=(two*L)/((one-Z).pow(2)*B.pow(2));t=(A.pow(3)+three*A*B.pow(2))/four
v=C+C*LC-M-two*mu*t/three-mu*C.pow(3)/three
emit(f'  have hv := {v.h}')
emit(f'  have hel := balancedEL_multiplier_cost (branch_balancedEL (z := {q(z)}) (by norm_num) (by norm_num))')
emit(f'  have he : balancedPenalty (branchMu {q(z)}/3) (branchA {q(z)}) (branchB {q(z)})-constantPenalty (branchMu {q(z)}/3) {q(c)} = {v.e} := by')
emit('    dsimp only ['+','.join(f'v{i}' for i in range(1,Node.count+1))+']')
emit('    unfold balancedPenalty constantPenalty entropy\n    rw [show balancedCost (branchA '+q(z)+') (branchB '+q(z)+')=1-(branchA '+q(z)+'+branchB '+q(z)+')/2-branchMu '+q(z)+'*balancedTriangle (branchA '+q(z)+') (branchB '+q(z)+') by linarith [hel]]')
emit('    unfold branchA branchMu balancedTriangle\n    ring')
emit('  rw [he]\n  exact lt_of_lt_of_le (by norm_num) hv.1\n')
emit('theorem penalizedGap_smallUpper_pos : 0<penalizedGap smallParameterUpper := by')
emit('  have hz : smallParameterUpper∈Ioo (0:ℝ) 1 := by norm_num [smallParameterUpper]')
emit('  have hγ : 0<branchMu smallParameterUpper/3 := div_pos (branchMu_pos hz.1 hz.2) (by norm_num)')
emit(f'  have ht := constantPenalty_min hγ (by norm_num : {q(c)}∈Icc (0:ℝ) 1)')
emit('  rw [penalizedGap_eq hz.1]\n  have hg := smallUpper_trial_gap\n  norm_num only [smallParameterUpper] at ht ⊢\n  linarith\n')
emit('theorem penalizedCrossing_lt_smallUpper : penalizedCrossing<smallParameterUpper := by')
emit('  rcases lt_trichotomy penalizedCrossing smallParameterUpper with h | h | h\n  · exact h\n  · have hh := penalizedGap_smallUpper_pos\n    rw [←h,penalizedCrossing_spec.2] at hh\n    linarith\n  · have hh := penalizedGap_neg_before ⟨by norm_num [smallParameterUpper],h⟩\n    linarith [penalizedGap_smallUpper_pos]\n')
emit('end SparseLowerTail.Section07')
Path('SparseLowerTail/Section07/PenalizedUpper.lean').write_text(header+'\n'.join(cg.lines)+'\n')
print('Proposed gap lower',float(v.l),'upper',float(v.u))
