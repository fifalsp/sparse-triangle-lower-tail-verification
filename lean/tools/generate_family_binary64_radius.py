#!/usr/bin/env python3
"""Reuse the checked AAA interval data at the manuscript's exact binary64 radius.

Only proofs of geometric containment are changed; the five numerical Hessian
certificates are imported unchanged. Lean checks the larger-radius conclusions.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
src=(ROOT/'SparseLowerTail/Section08/FamilyAAACover.lean').read_text()
parts=['''import SparseLowerTail.Section08.FamilyAAACover

/-! The exact binary64 radius in Appendix A.3. The existing five AAA
Hessian certificates have enough geometric padding for this larger cube. -/
noncomputable section
namespace SparseLowerTail.Certificate.ManuscriptFamilyRadius
open Numerics Section04 Set

/-- The binary64 value of 0.1, written as its exact rational value. -/
def binary64Radius : ℝ := 3602879701896397/36028797018963968

theorem binary64Radius_pos : 0 < binary64Radius := by
  norm_num [binary64Radius]

theorem binary64Radius_error :
    binary64Radius - 1/10 = 1/180143985094819840 := by
  norm_num [binary64Radius]

theorem tenth_lt_binary64Radius : (1/10 : ℝ) < binary64Radius := by
  norm_num [binary64Radius]

/-- It lies within half a binary64 spacing of 1/10 in its binade. -/
theorem binary64Radius_half_ulp :
    |binary64Radius - 1/10| < 1/144115188075855872 := by
  norm_num [binary64Radius]
''']
for i in range(5):
 block=src.split(f'namespace Leaf{i}\n',1)[1].split(f'end Leaf{i}',1)[0]
 proof=block[block.index('theorem cube_in_box'):]
 assert proof.count('(1/10)')==2 and proof.count('(1/10:ℝ)')==1
 proof=proof.replace('(1/10)','binary64Radius').replace('(1/10:ℝ)','binary64Radius')
 proof=proof.replace('  have hh := abs_le.mp hqi','  norm_num only [binary64Radius] at hqi\n  have hh := abs_le.mp hqi')
 parts.append(f'\nnamespace AAA{i}\nopen FamilyAAACover.Leaf{i}\n'+proof+f'end AAA{i}\n')
parts.append('''
/-- The full AAA Hessian conclusion on the manuscript's closed cube. -/
theorem aaa_hessian_positive {z : ℝ} (hz : 0 < z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q ∈ familyCube (familyContactAAA z) binary64Radius)
    {v : FamilyVector} (hv : v ≠ 0) : 0 < familyHessianForm z q v := by
  rcases FamilyAAACover.parameter_covered hL with h | h | h | h | h
  · exact AAA0.hessian_positive hz h hq hv
  · exact AAA1.hessian_positive hz h hq hv
  · exact AAA2.hessian_positive hz h hq hv
  · exact AAA3.hessian_positive hz h hq hv
  · exact AAA4.hessian_positive hz h hq hv

/-- The full AAA local minimum and exact zero at the manuscript's radius. -/
theorem aaa_local_nonnegative_and_unique_zero {z : ℝ} (hz : 0 < z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q ∈ familyCube (familyContactAAA z) binary64Radius) :
    0 ≤ familyPhi z q ∧ (familyPhi z q = 0 ↔ q = familyContactAAA z) := by
  have hz40 := FamilyAAACover.z_le_one_fortieth hz hL
  have hz1 : z < 1 := by linarith
  exact familyContactAAA_local hz hz1 (gamma_branch_neg hz hz40).ne
    binary64Radius_pos.le (fun _ hq _ hv => aaa_hessian_positive hz hL hq hv) hq

end SparseLowerTail.Certificate.ManuscriptFamilyRadius
''')
(ROOT/'SparseLowerTail/Section08/ManuscriptFamilyRadius.lean').write_text(''.join(parts))
if __name__=='__main__':
 print('Generated ManuscriptFamilyRadius.lean from five existing checked AAA certificates.')
