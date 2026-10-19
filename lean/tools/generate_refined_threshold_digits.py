#!/usr/bin/env python3
"""Refine the actual crossing bracket, using the existing proof generator.
Decimal bisection proposes numbers only; Lean rechecks all signs and bounds.
The original ThresholdDigits source is never rewritten by this script.
"""
from decimal import Decimal,localcontext,ROUND_FLOOR
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
 with localcontext() as ctx:
  ctx.prec=75
  def value(z):
   t=(z**3+3*z)/4;k=(t.ln()/3).exp();L=-z.ln()
   return ((1+z)/2-k)*(1+2*z*L/(1-z)**2)+z*L/2-k*(-t.ln())/3
  lo=Decimal('0.02005543105488');hi=Decimal('0.02005543105489')
  for _ in range(100):
   mid=(lo+hi)/2
   if value(mid)>0:lo=mid
   else:hi=mid
  n=int((mid*10**18).to_integral_value(rounding=ROUND_FLOOR))
 zlo,zhi=F(n-1,10**18),F(n+2,10**18)
 src=(ROOT/'tools/generate_threshold_digits.py').read_text()
 marker='emit("""\n/-- The four parameter enclosures over the entire printed z bracket.'
 assert src.count(marker)==1
 src=src.split(marker)[0]
 old='zs=[F(2005543105488,10**14),F(2005543105489,10**14)]'
 assert src.count(old)==1
 src=src.replace(old,f'zs=[F({zlo.numerator},{zlo.denominator}),F({zhi.numerator},{zhi.denominator})]')
 src=src.replace('def bounds(d,p=20):','def bounds(d,p=21):')
 src=src.replace('namespace SparseLowerTail.Section04\n',f'namespace SparseLowerTail.Section04.Refined\n\ndef digitZLower : ℝ := {zlo.numerator}/{zlo.denominator}\ndef digitZUpper : ℝ := {zhi.numerator}/{zhi.denominator}\n')
 src=src.replace('tools/generate_threshold_digits.py.', 'tools/generate_refined_threshold_digits.py.')
 env={};exec(compile(src,'existing_threshold_generator','exec'),env)
 emit=env['emit'];q=env['q'];Node=env['Node'];lines=env['lines']
 start=len(lines)
 Z=Node('z',zlo,zhi,'hZ');L=Node('(branchLog z)',env['Ll'],env['Lu'],'hL');B=Node('(branchB z)',env['Blo'],env['Bhi'],'hB')
 one=Node.c(1);two=Node.c(2)
 A=Z*B;mu=(two*L)/((one-Z)*(one-Z)*(B*B))
 calculation=lines[start:];del lines[start:]
 emit(f'theorem tight_branch_ranges {{z : ℝ}} (hz : z ∈ Set.Icc digitZLower digitZUpper) :\n    Bounds (branchA z) {q(A.lo)} {q(A.hi)} ∧\n    Bounds (branchB z) {q(B.lo)} {q(B.hi)} ∧\n    Bounds (branchMu z) {q(mu.lo)} {q(mu.hi)} := by')
 emit(f'  have hZ : Bounds z {q(zlo)} {q(zhi)} := by\n    unfold Bounds\n    norm_num [digitZLower,digitZUpper] at hz\n    exact hz')
 emit('  have hL := digit_log_range hz\n  have hB := digit_branchB_range hz')
 lines.extend(calculation)
 emit('  refine ⟨?_,hB,?_⟩')
 emit(f'  · exact {A.h}')
 emit(f'  · convert {mu.h} using 1 <;> norm_num [branchMu,pow_two]')
 emit('\nend SparseLowerTail.Section04.Refined')
 output=ROOT/'SparseLowerTail/Section04/RefinedThresholdDigits.lean'
 text=env['base']+'\n'.join(lines)+'\n'
 for tag in ['lower','upper']:
  text=text.replace(f'convert digit_normalized_{tag} using 1\n  norm_num',f'convert digit_normalized_{tag} using 1 <;> norm_num')
 output.write_text(text)
 print('Proposed crossing bracket:',zlo,zhi,'width',zhi-zlo)
 print('Proposed widths: a',float(A.hi-A.lo),'b',float(B.hi-B.lo),'mu',float(mu.hi-mu.lo))
if __name__=='__main__':main()
