#!/usr/bin/env python3
"""Emit exact rational arithmetic for smallparams(b)'s error table. Run in lean/."""
from pathlib import Path
from fractions import Fraction as F
import cover_interval_codegen as cg
N=cg.Node;emit=cg.emit
header='''import SparseLowerTail.Section07.SmallErrorBounds

/-! The ten-term error table from lem:smallparams(b), with actual error
expressions. Generated rational arithmetic is checked by the Lean kernel. -/
noncomputable section
namespace SparseLowerTail.Section07.SmallErrorData
open Numerics
'''

for kind,limit in [('mean',F(549,10000)),('codegree',F(699,10000)),('base',F(1633,100000))]:
 N.count=0
 def node(e,l,u,proof):return N(e,F(l),F(u),proof)
 M=node('d.bound',1,F(10013,10000),'d.bound_bounds')
 M2=node('(d.bound^2)',1,F(1002575,1000000),'d.bound_sq_bounds')
 m=node('d.m',F(4992,10000),F(1,2),'d.mean_bounds')
 ev=node('d.ev',F(4989,10000),F(1,2),'d.eigenvalue_bounds')
 eta=node('d.eta',0,F(6,10000),'d.eta_bounds')
 H=node('(d.mu*d.eta)',0,F(115,10000),'d.mu_eta_bounds')
 J=node('(d.mu*d.tail)',0,F(1608,1000000),'d.mu_tail_bounds')
 K=node('(d.ev*d.mu*(d.bound-1))',0,F(12304,1000000),'d.scaled_bound_defect_bounds')
 D=node('(d.mu*(1/2-d.m))',0,F(155,10000),'d.mean_defect_bounds')
 P=node('(d.mu*Real.sqrt (d.diagonal*d.tail*d.eta*d.m/2))',0,F(1523,1000000),'d.weighted_sqrt_codegree_bounds')
 Q=node('(d.mu*Real.sqrt (d.tail*d.diagonal)*Real.sqrt (2-2/d.bound))',0,F(6305,1000000),'d.weighted_sqrt_mean_bounds')
 R=node('(Real.sqrt (d.eta*d.m/2))',0,F(1225,100000),'d.sqrt_eta_mean_bounds')
 S=node('(Real.sqrt (d.tail*d.diagonal))',0,F(66,10000),'d.sqrt_tail_diagonal_bounds')
 args='d.eta d.ev d.bound d.tail d.diagonal' if kind=='mean' else 'd.eta d.m d.ev d.bound d.tail d.diagonal'
 name='rowMeanError' if kind=='mean' else 'rowCodegreeError'
 if kind=='base':name='rowBaseError';args='d.m d.eta d.ev d.bound'
 emit(f'theorem weighted_{kind}_upper (d : SmallErrorData) :')
 emit(f'    d.mu*{name} {args}<{cg.q(limit)} := by')
 if kind=='mean':v=H*(N.c(2)*M2-N.c(1))+N.c(3)*M*K+M2*Q
 if kind=='codegree':v=H*m/N.c(2)+N.c(2)*ev*M2*H+P+N.c(4)*M2*(m+eta)*H+N.c(2)*M2*J*R+N.c(5)*ev*M*K+N.c(2)*M2*J*S
 if kind=='base':v=D*(m+eta)+ev*M*(D+J)
 emit(f'  have he : d.mu*{name} {args}={v.e} := by')
 emit('    dsimp only ['+','.join(f'v{i}' for i in range(1,N.count+1))+']')
 emit(f'    unfold {name}')
 if kind=='base':
  emit('    rw [abs_of_nonpos (by linarith [d.mean_upper]),abs_of_nonpos (by linarith [d.eigenvalue_upper,d.mean_upper])]')
  emit('    dsimp [tail]')
 emit('    ring')
 emit(f'  rw [he]\n  exact lt_of_le_of_lt {v.h}.2 (by norm_num)\n')
 print(kind,'checked proposal upper',float(v.u),'target',float(limit))
emit('end SparseLowerTail.Section07.SmallErrorData')
Path('SparseLowerTail/Section07/SmallErrorSums.lean').write_text(header+'\n'.join(cg.lines)+'\n')
