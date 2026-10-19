#!/usr/bin/env python3
"""Propose a shared-register program; Lean proves all 13 expression identities."""
import gzip
import json
from fractions import Fraction as F
from pathlib import Path
from generate_exp_endpoints import rat
ROOT=Path(__file__).resolve().parents[1]
d=json.loads(gzip.decompress((ROOT/'data/cover-job-expression-dag.json.gz').read_bytes()))
code=[]
for op,*a in d['nodes']:
    if op=='r':s='.rational '+rat(F(*a))
    elif op=='v':s='.var '+str(a[0])
    elif op=='-':s='.neg '+str(a[0])
    elif op in ('+','*'):s=('.add ' if op=='+' else '.mul ')+str(a[0])+' '+str(a[1])
    else:raise ValueError('Unsupported operation')
    code.append(s)
r=d['roots'];roots=[r['value']]+r['gradient']+[x for row in r['hessian'] for x in row]
labels=['Value']+[f'Gradient{i}' for i in range(3)]+[f'Hessian{i}{j}' for i in range(3) for j in range(3)]
targets=['apexCertificateExpr']+[f'coverGradientExpr {i}' for i in range(3)]+[f'coverHessianExpr {i} {j}' for i in range(3) for j in range(3)]
s='''import SparseLowerTail.Numerics.IntervalProgram
import SparseLowerTail.Section05.CoverRefinedJobTaylorBox

/-! Shared-register program for every actual nonapex job. The untrusted
export/generator proposes instructions; all thirteen output identities must
be checked by the kernel against the original mathematical expressions. -/
namespace SparseLowerTail.Section05.CoverJobProgram
open Numerics PolynomialExpr
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
s+=f'def depth : ℕ := {(len(code)-1).bit_length()}\ndef code : List (IntervalInstruction 24) :=\n  ['+',\n   '.join(code)+']\n'
for label,k,target in zip(labels,roots,targets):
    s+=f'''\ndef output{label} : ℕ := {k}
theorem output{label}_eq :
    (IntervalProgram.symbolic code depth).get output{label} = {target} := by
  decide +kernel
'''
s+='\nend SparseLowerTail.Section05.CoverJobProgram\n'
(ROOT/'SparseLowerTail/Section05/CoverJobProgram.lean').write_text(s)
print(f'{len(code)} instructions; {len(roots)} symbolic identities proposed')
