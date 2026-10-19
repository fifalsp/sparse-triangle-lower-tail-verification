#!/usr/bin/env python3
"""Generate selected scaled-Hessian leaf proofs, never a full-cover claim."""
import json
from fractions import Fraction as F
from pathlib import Path
from generate_exp_endpoints import rat
from generate_family_leaf_example import I, S, ep, expbox, coeff

ROOT = Path(__file__).resolve().parents[1]


def main():
    data = json.loads((ROOT/'data/family-scaled-smoke-proposal.json').read_text())
    if not data['scaled']:
        raise ValueError('Expected scaled-Hessian data')
    lines = ['import SparseLowerTail.Section08.FamilyOffsetCover', '',
             '/-! Two selected mixed-contact Hessian boxes. Not a full cover. -/',
             'namespace SparseLowerTail.Certificate.FamilyScaledSmoke',
             'open Numerics Section04', 'set_option maxRecDepth 100000',
             'set_option maxHeartbeats 8000000', '']
    for index, row in enumerate(data['leaves']):
        lo, hi = F(row['lower'][0]), F(row['upper'][0])
        qlo, qhi = list(map(F, row['qLower'])), list(map(F, row['qUpper']))
        elo, ehi = ep(lo), ep(hi)
        L, z = I(I(lo).l, I(hi).u), expbox(elo, ehi)
        delta = 2*z*L/(1-z)**2
        dlo, dhi = ep(F(delta.l, S)), ep(F(delta.u, S))
        cs = coeff(z, L, expbox(dlo, dhi))
        lines += [f'namespace Leaf{index}']
        endpoints = dict(logLower=elo, logUpper=ehi, deltaLower=dlo, deltaUpper=dhi)
        for i in range(3):
            endpoints[f'qLower{i}'], endpoints[f'qUpper{i}'] = ep(qlo[i]), ep(qhi[i])
            for j in range(i+1, 3):
                endpoints[f'pLower{i}{j}'] = ep((qlo[i]+qlo[j])/2)
                endpoints[f'pUpper{i}{j}'] = ep((qhi[i]+qhi[j])/2)
        for name, (q, n, l, u, lb, ub) in endpoints.items():
            lines += [f'def {name} : ExpEndpointCertificate :=',
                      f'  ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(lb)},{rat(ub)}⟩',
                      f'theorem {name}_valid : {name}.Valid := by decide +kernel']
        lines += ['def parameter : FamilyParameterCertificate :=',
                  f'  ⟨logLower,logUpper,deltaLower,deltaUpper,{delta.lean()}⟩',
                  'theorem parameter_valid : parameter.Valid := by',
                  '  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩',
                  '  all_goals decide +kernel',
                  'def box : FamilyBoxCertificate :=',
                  '  ⟨parameter,!['+','.join(c.lean() for c in cs)+'],',
                  '    ![qLower0,qLower1,qLower2],![qUpper0,qUpper1,qUpper2]⟩',
                  'theorem box_valid : box.Valid := by',
                  '  refine ⟨parameter_valid,?_,?_,?_⟩',
                  '  · intro i; fin_cases i <;> decide +kernel',
                  '  · intro i; fin_cases i',
                  *[f'    · exact qLower{i}_valid' for i in range(3)],
                  '  · intro i; fin_cases i',
                  *[f'    · exact qUpper{i}_valid' for i in range(3)]]
        for bound in ['Lower', 'Upper']:
            rows = []
            for i in range(3):
                rows.append('!['+','.join(f'q{bound}{i}' if i == j else
                    f'p{bound}{min(i,j)}{max(i,j)}' for j in range(3))+']')
            lines += [f'def pair{bound} : Fin 3 → Fin 3 → ExpEndpointCertificate :=',
                      '  !['+','.join(rows)+']']
        lines += ['def certificate : FamilyScaledBoxCertificate := ⟨box,pairLower,pairUpper⟩',
                  'theorem certificate_valid : certificate.Valid := by',
                  '  refine ⟨box_valid,?_⟩',
                  '  intro i j hij', '  fin_cases i <;> fin_cases j',
                  '  all_goals first | exact (hij rfl).elim | skip']
        for i in range(3):
            for j in range(3):
                if i != j:
                    a, b = min(i,j), max(i,j)
                    lines += [f'  · exact ⟨pLower{a}{b}_valid,pUpper{a}{b}_valid,by decide +kernel,by decide +kernel⟩']
        lines += ['def transform : FamilyRationalMatrix := !['+
                  ','.join('!['+','.join(rat(F(x)) for x in r)+']' for r in row['transform'])+']',
                  'theorem margins_checked : FamilyIntervalPositive',
                  '    (familyIntervalCongruence certificate.hessianIntervals transform) := by decide +kernel',
                  'theorem hessian_positive {z : ℝ} (hz : 0<z)',
                  '    (hL : Bounds (branchLog z) (parameter.logLower.q : ℝ) (parameter.logUpper.q : ℝ))',
                  '    {q : FamilyVector}',
                  '    (hq : ∀i,Bounds (q i) ((box.qLower i).q : ℝ) ((box.qUpper i).q : ℝ))',
                  '    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=',
                  '  certificate.hessian_positive certificate_valid transform margins_checked hz hL hq hv',
                  'def offsetBox : ReplayBox 4 := ⟨!['+', '.join(rat(F(x)) for x in row['lower'])+'],!['+', '.join(rat(F(x)) for x in row['upper'])+']⟩',
                  'theorem encloses_offsets : box.EnclosesABBOffsets offsetBox := by decide +kernel',
                  'theorem offset_hessian_positive {z : ℝ} (hz : 0<z) (hz1 : z<1)',
                  '    {q : FamilyVector} (hq : offsetBox.Contains (familyABBOffsetCoordinates z q))',
                  '    {v : FamilyVector} (hv : v≠0) : 0<familyHessianForm z q v :=',
                  '  certificate.abb_offset_hessian_positive certificate_valid transform margins_checked',
                  '    encloses_offsets hz hz1 hq hv',
                  f'end Leaf{index}', '']
    lines += ['end SparseLowerTail.Certificate.FamilyScaledSmoke', '']
    (ROOT/'SparseLowerTail/Section08/FamilyScaledSmoke.lean').write_text('\n'.join(lines))
    print(f'Generated {len(data["leaves"])} selected leaf proofs; no coverage claim.')


if __name__ == '__main__':
    main()
