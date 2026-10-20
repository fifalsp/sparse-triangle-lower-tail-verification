#!/usr/bin/env python3
"""Reuse the rational certificate emitter for the current proof's z=1/1000 test."""
from pathlib import Path
from fractions import Fraction as F
import cover_interval_codegen as cg
root=Path(__file__).resolve().parents[1]
src=(root/'tools/generate_penalized_digits.py').read_text()
marker="lo,hi=Decimal('8.352460192e-5')"
assert src.count(marker)==1
prefix=src.split(marker)[0]
assert prefix.count(',14,90)')==2
prefix=prefix.replace(',14,90)',',10,90)')
env={};exec(compile(prefix,'penalized_endpoint_emitter','exec'),env)
branch_data,logcert,q,emit,Node,unfolds=(env[x]for x in ['branch_data','logcert','q','emit','Node','unfolds'])
d=branch_data('milli',F(1,1000),F(1,1000))
z=F(1,1000);c=F(3,10);cl,cu=logcert('trial_log',c,2,60)
Node.count=0;start=len(cg.lines)
M=Node('(branchMu '+q(z)+')',d['mu'].l,d['mu'].u,'hM');C=Node.c(c);LC=Node('(-Real.log '+q(c)+')',cl,cu,'trial_log')
V=Node.c(1)-C-C*LC+M*C.pow(3)/Node.c(3)
calc=cg.lines[start:];del cg.lines[start:]
assert V.u<F(468,1000)
emit(f'theorem trial_penalty_lt : constantPenalty (branchMu {q(z)}/3) {q(c)}<(468/1000:ℝ) := by\n  have hM := (milli_data (z := {q(z)}) ⟨le_rfl,le_rfl⟩).1');cg.lines.extend(calc)
emit(f'  have he : constantPenalty (branchMu {q(z)}/3) {q(c)}={V.e} := by\n    dsimp only [{unfolds()}]\n    unfold constantPenalty entropy\n    ring\n  rw [he]\n  exact lt_of_le_of_lt {V.h}.2 (by norm_num)\n')
emit('theorem milli_branch_penalty_gt : (496/1000:ℝ)<balancedPenalty (branchMu (1/1000)/3) (branchA (1/1000)) (branchB (1/1000)) := by\n  have h := (milli_data (z := (1/1000:ℝ)) ⟨le_rfl,le_rfl⟩).2.2.2.2\n  exact lt_of_lt_of_le (by norm_num) h.1\n')
emit('theorem milli_constant_minimum_lt : constantMinimum (branchMu (1/1000)/3)<(468/1000:ℝ) := by\n  have hγ : 0<branchMu (1/1000)/3 := div_pos (branchMu_pos (by norm_num) (by norm_num)) (by norm_num)\n  exact (constantPenalty_min hγ (by norm_num : (3/10:ℝ) ∈ Icc (0:ℝ) 1)).trans_lt trial_penalty_lt\n')
emit('theorem milli_gap_gt : (28/1000:ℝ)<penalizedGap (1/1000) := by\n  rw [penalizedGap_eq (by norm_num : (0:ℝ)<1/1000)]\n  have hl := milli_branch_penalty_gt\n  have hu := milli_constant_minimum_lt\n  change constantPenalty (branchMu (1/1000)/3) (constantRoot (branchMu (1/1000)/3))<468/1000 at hu\n  linarith\n')
header='''import SparseLowerTail.Section07.PenalizedDigitsCore

/-! Exact numerical bounds used in the current proof of lem:tie. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07.EndpointProof
open Section04 Numerics
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
'''
(root/'SparseLowerTail/Section07/PenalizedEndpointProof.lean').write_text(header+'\n'.join(cg.lines)+'\nend SparseLowerTail.Section07.EndpointProof\n')
print('Proposed trial penalty upper',float(V.u))
