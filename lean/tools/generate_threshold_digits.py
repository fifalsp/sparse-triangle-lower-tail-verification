#!/usr/bin/env python3
"""Emit rational Lean certificates; Lean checks every analytic/arithmetic bound.
Decimal values only choose proposed brackets; they have no trusted role.
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext, ROUND_FLOOR
from pathlib import Path
getcontext().prec=75
out=Path('SparseLowerTail/Section04/ThresholdDigits.lean')
base = """import SparseLowerTail.Section04.ThresholdDefinitions
import SparseLowerTail.Section04.BalancedPhase

/-! Generated proof certificate for manuscript lem:digits.
Regenerate from the lean directory with python3 tools/generate_threshold_digits.py.
All decimal proposals are validated by the Lean kernel using proved Taylor bounds.
-/
noncomputable section
open SparseLowerTail.Numerics
namespace SparseLowerTail.Section04

"""
lines=[]
def emit(s=''): lines.append(s)
def q(v):
 v=F(v)
 return f'({v.numerator}/{v.denominator} : ℝ)' if v.denominator!=1 else f'({v.numerator} : ℝ)'
def dec(f): return Decimal(f.numerator)/Decimal(f.denominator)
def bounds(d,p=20):
 lo=int((d*Decimal(10)**p).to_integral_value(rounding=ROUND_FLOOR))
 return F(lo-1,10**p),F(lo+2,10**p)
def log_cert(name,x,d,n):
 lo,hi=bounds(d)
 emit(f'theorem {name} : Bounds (-Real.log {q(x)}) {q(lo)} {q(hi)} := by')
 emit(f'  have h := Real.abs_log_sub_add_sum_range_le (x := {q(1-64*x)}) (by norm_num) {n}')
 emit('  norm_num [Finset.sum_range_succ] at h')
 emit('  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2')
 emit(f'  have he : Real.log {q(64*x)} = 6*Real.log 2 + Real.log {q(x)} := by')
 emit(f'    rw [show {q(64*x)} = (2:ℝ)^6 * {q(x)} by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]')
 emit('    norm_num')
 emit('  rw [he] at hl hu')
 emit('  have h2l := log_two_bounds_22.1\n  have h2u := log_two_bounds_22.2')
 emit('  constructor <;> linarith\n')
 return lo,hi
class Node:
 i=0
 def __init__(self,e,lo,hi,h):self.e,self.lo,self.hi,self.h=e,F(lo),F(hi),h
 def c(v):return Node(q(v),v,v,f'(Bounds.refl {q(v)})')
 def op(self,y,typ):
  if typ=='+':l,u=self.lo+y.lo,self.hi+y.hi; proof=f'{self.h}.add {y.h}'
  elif typ=='-':l,u=self.lo-y.hi,self.hi-y.lo;proof=f'{self.h}.sub {y.h}'
  elif typ=='*':
   assert self.lo>=0 and y.lo>=0
   l,u=self.lo*y.lo,self.hi*y.hi;proof=f'{self.h}.mul_nonneg {y.h} (by norm_num) (by norm_num)'
  elif typ=='/':
   assert self.lo>=0 and y.lo>0
   l,u=self.lo/y.hi,self.hi/y.lo;proof=f'{self.h}.div_pos {y.h} (by norm_num) (by norm_num)'
  # Round outward, keeping intermediate certificate integers small.
  scale=10**24;l=F(l.numerator*scale//l.denominator,scale);u=F(-((-u.numerator*scale)//u.denominator),scale)
  Node.i+=1;h=f'h{Node.i}';e=f'({self.e}{typ}{y.e})'
  emit(f'  have {h} : Bounds {e} {q(l)} {q(u)} := by')
  emit(f'    exact ({proof}).weaken (by norm_num) (by norm_num)')
  return Node(e,l,u,h)
 def __add__(s,y):return s.op(y,'+')
 def __sub__(s,y):return s.op(y,'-')
 def __mul__(s,y):return s.op(y,'*')
 def __truediv__(s,y):return s.op(y,'/')

zs=[F(2005543105488,10**14),F(2005543105489,10**14)]
for tag,z in zip(['lower','upper'],zs):
 t=(z**3+3*z)/4;zd=dec(z);td=dec(t)
 ll,lu=log_cert(f'digit_log_z_{tag}',z,-zd.ln(),40)
 tl,tu=log_cert(f'digit_log_t_{tag}',t,-td.ln(),18)
 kl,ku=bounds((td.ln()/3).exp())
 emit(f'theorem digit_kappa_{tag} : Bounds (kappa {q(z)}) {q(kl)} {q(ku)} := by')
 emit(f'  have hc := kappa_cube (z := {q(z)}) (by norm_num)')
 emit('  constructor')
 for bound,which in [(kl,'lower'),(ku,'upper')]:
  emit('  · apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp')
  emit('    rw [hc]')
  emit('    norm_num')
 emit('')
 emit(f'theorem digit_normalized_{tag} : '+ ('0 < ' if tag=='lower' else '') +f'normalizedDifference {q(z)}'+(' < 0' if tag=='upper' else '')+' := by')
 L=Node(f'(-Real.log {q(z)})',ll,lu,f'digit_log_z_{tag}')
 T=Node(f'(-Real.log {q(t)})',tl,tu,f'digit_log_t_{tag}')
 K=Node(f'(kappa {q(z)})',kl,ku,f'digit_kappa_{tag}')
 Z=Node.c(z);one=Node.c(1);two=Node.c(2);three=Node.c(3)
 M=(one+Z)/two; den=(one-Z)*(one-Z);E=(two*Z*L)/den
 val=(M-K)*(one+E)+(Z*L)/two-(K*T)/three
 emit(f'  have hv := {val.h}')
 emit(f'  have he : normalizedDifference {q(z)} = {val.e} := by')
 emit('    unfold normalizedDifference\n    rw [branchLog_eq_neg_log]\n    norm_num')
 emit('  rw [← he] at hv')
 emit('  unfold Bounds at hv\n  linarith\n')

emit('theorem digit_D_lower : 0 < branchDifference digitZLower := by')
emit('  rw [branchDifference_normalized (by norm_num [digitZLower])]')
emit('  apply mul_pos (branchB_pos _)\n  convert digit_normalized_lower using 1\n  norm_num [digitZLower]')
emit('')
emit('theorem digit_D_upper : branchDifference digitZUpper < 0 := by')
emit('  rw [branchDifference_normalized (by norm_num [digitZUpper])]')
emit('  apply mul_neg_of_pos_of_neg (branchB_pos _)\n  convert digit_normalized_upper using 1\n  norm_num [digitZUpper]')
emit('')
emit('end SparseLowerTail.Section04')

lines.pop()
emit("""
/-- The crossing lies strictly inside the printed decimal bracket. -/
theorem transitionParameter_digits : digitZLower < transitionParameter ∧ transitionParameter < digitZUpper := by
  constructor
  · rcases lt_trichotomy digitZLower transitionParameter with hl | he | hr
    · exact hl
    · have h := digit_D_lower
      rw [he, branchDifference_transition] at h
      linarith
    · have h := branchDifference_neg_after_transition ⟨hr, by norm_num [digitZLower]⟩
      linarith [digit_D_lower]
  · rcases lt_trichotomy transitionParameter digitZUpper with hl | he | hr
    · exact hl
    · have h := digit_D_upper
      rw [← he, branchDifference_transition] at h
      linarith
    · have h := branchDifference_pos_before_transition ⟨by norm_num [digitZUpper], hr⟩
      linarith [digit_D_upper]
""")
zlo,zhi=zs
tlo,thi=(zlo**3+3*zlo)/4,(zhi**3+3*zhi)/4
Ll=bounds(-dec(zhi).ln())[0]; Lu=bounds(-dec(zlo).ln())[1]
Kl=bounds((dec(tlo).ln()/3).exp())[0]; Ku=bounds((dec(thi).ln()/3).exp())[1]
emit(f'theorem digit_log_range {{z : ℝ}} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchLog z) {q(Ll)} {q(Lu)} := by')
emit('  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num [digitZLower]) hz.1')
emit('  have hl := Real.log_le_log (show 0 < digitZLower by norm_num [digitZLower]) hz.1')
emit('  have hu := Real.log_le_log hz0 hz.2')
emit('  have hll := digit_log_z_upper.1\n  have hlu := digit_log_z_lower.2')
emit('  norm_num [digitZLower, digitZUpper] at hl hu\n  rw [branchLog_eq_neg_log]\n  constructor <;> linarith\n')
emit(f'theorem digit_kappa_range {{z : ℝ}} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (kappa z) {q(Kl)} {q(Ku)} := by')
emit('  have hz0 : 0 ≤ z := le_trans (by norm_num [digitZLower]) hz.1')
emit('  have hpowlo := pow_le_pow_left₀ (show 0 ≤ digitZLower by norm_num [digitZLower]) hz.1 3')
emit('  have hpowhi := pow_le_pow_left₀ hz0 hz.2 3')
emit('  have hlo : kappa digitZLower ≤ kappa z := by\n    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp\n    rw [kappa_cube (by norm_num [digitZLower]), kappa_cube hz0]\n    nlinarith [hz.1]')
emit('  have hhi : kappa z ≤ kappa digitZUpper := by\n    apply (show Odd (3 : ℕ) by decide).strictMono_pow.le_iff_le.mp\n    rw [kappa_cube hz0, kappa_cube (by norm_num [digitZUpper])]\n    nlinarith [hz.2]')
emit('  have hkl := digit_kappa_lower.1\n  have hku := digit_kappa_upper.2\n  norm_num [digitZLower, digitZUpper] at hlo hhi\n  constructor <;> linarith\n')
start=len(lines)
Z=Node('z',zlo,zhi,'hZ');L=Node('(branchLog z)',Ll,Lu,'hL');one=Node.c(1);two=Node.c(2)
den=(one-Z)*(one-Z);E=(two*Z*L)/den
calc=lines[start:];del lines[start:]
emit(f'theorem digit_exponent_range {{z : ℝ}} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (2*z*branchLog z/(1-z)^2) {q(E.lo)} {q(E.hi)} := by')
emit(f'  have hZ : Bounds z {q(zlo)} {q(zhi)} := by\n    unfold Bounds\n    norm_num [digitZLower, digitZUpper] at hz\n    exact hz')
emit('  have hL := digit_log_range hz')
lines.extend(calc)
emit(f'  convert {E.h} using 1\n  ring\n')

def exp_cert(name,x):
 lo,hi=bounds(dec(x).exp())
 emit(f'theorem {name} : Bounds (Real.exp {q(x)}) {q(lo)} {q(hi)} := by')
 emit(f'  have h := Real.exp_bound (x := {q(x)}) (by norm_num) (n := 20) (by norm_num)')
 emit('  norm_num [Finset.sum_range_succ, Nat.factorial] at h')
 emit('  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2\n  constructor <;> linarith\n')
 return lo,hi
Blo=exp_cert('digit_exp_lower',-E.hi)[0]
Bhi=exp_cert('digit_exp_upper',-E.lo)[1]
emit(f'theorem digit_branchB_range {{z : ℝ}} (hz : z ∈ Set.Icc digitZLower digitZUpper) : Bounds (branchB z) {q(Blo)} {q(Bhi)} := by')
emit('  have hE := digit_exponent_range hz')
emit('  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)\n  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)')
emit('  have he : branchB z = Real.exp (-(2*z*branchLog z/(1-z)^2)) := by unfold branchB; congr 1; ring')
emit('  rw [← he] at hlo hhi\n  have hbl := digit_exp_lower.1\n  have hbu := digit_exp_upper.2\n  constructor <;> linarith\n')
emit("""
/-- The four parameter enclosures over the entire printed z bracket. -/
theorem digit_branch_ranges {z : ℝ} (hz : z ∈ Set.Icc digitZLower digitZUpper) :
    Bounds (branchA z) (1703401908/10^11) (1703401909/10^11) ∧
    Bounds (branchB z) (8493469443/10^10) (8493469444/10^10) ∧
    Bounds (branchMu z) (1128627816/10^8) (1128627817/10^8) ∧
    Bounds (branchRho z) (2096696762/10^10) (2096696763/10^10) := by
""")
emit(f'  have hZ : Bounds z {q(zlo)} {q(zhi)} := by\n    unfold Bounds\n    norm_num [digitZLower, digitZUpper] at hz\n    exact hz')
emit('  have hL := digit_log_range hz\n  have hK := digit_kappa_range hz\n  have hB := digit_branchB_range hz')
Z=Node('z',zlo,zhi,'hZ');L=Node('(branchLog z)',Ll,Lu,'hL');K=Node('(kappa z)',Kl,Ku,'hK');B=Node('(branchB z)',Blo,Bhi,'hB')
A=Z*B;Bsq=B*B;den=(one-Z)*(one-Z);mu=(two*L)/(den*Bsq);rho=K*B
emit('  refine ⟨?_, ?_, ?_, ?_⟩')
emit(f'  · exact {A.h}.weaken (by norm_num) (by norm_num)')
emit('  · exact hB.weaken (by norm_num) (by norm_num)')
emit(f'  · have hm := {mu.h}.weaken (show {q(F(1128627816,10**8))} ≤ {q(mu.lo)} by norm_num) (show {q(mu.hi)} ≤ {q(F(1128627817,10**8))} by norm_num)')
emit('    convert hm using 1 <;> norm_num [branchMu, pow_two]')
emit(f'  · exact {rho.h}.weaken (by norm_num) (by norm_num)\n')
emit("""
/-- Lemma lem:digits for the exact mathematically defined crossing parameters. -/
theorem transition_digits :
    Bounds (branchA transitionParameter) (1703401908/10^11) (1703401909/10^11) ∧
    Bounds (branchB transitionParameter) (8493469443/10^10) (8493469444/10^10) ∧
    Bounds (branchMu transitionParameter) (1128627816/10^8) (1128627817/10^8) ∧
    Bounds transitionTarget (2096696762/10^10) (2096696763/10^10) := by
  have h := digit_branch_ranges ⟨le_of_lt transitionParameter_digits.1, le_of_lt transitionParameter_digits.2⟩
  rwa [branchRho_transitionParameter] at h

/-- The variationally defined threshold satisfies the printed enclosure. -/
theorem threshold_digits :
    Bounds threshold (2096696762/10^10) (2096696763/10^10) := by
  rw [threshold_eq_transitionTarget]
  exact transition_digits.2.2.2

end SparseLowerTail.Section04
""")
out.write_text((base+'-- BEGIN GENERATED CERTIFICATES\n\n'+'\n'.join(lines)).rstrip()+'\n')
