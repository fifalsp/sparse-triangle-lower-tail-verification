#!/usr/bin/env python3
"""Propose one complete exterior Taylor leaf; Lean checks every numeric fact.

The generated theorem covers a four-dimensional box, not the full domain.
The temporary #eval only proposes integer intervals; it is never a proof.
"""
from fractions import Fraction as F
from pathlib import Path
import re
import subprocess
import tempfile
from generate_exp_endpoints import rat
from generate_family_leaf_example import I, S, ep, expbox

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'SparseLowerTail/Section08/FamilyExteriorSmoke.lean'


def main():
    mid = F(4999,1280)
    em = ep(mid)
    z, L = expbox(em,em), I(mid)
    delta = 2*z*L/(1-z)**2
    endpoints = dict(midLog=em,deltaLower=ep(F(delta.l,S)),
                     deltaUpper=ep(F(delta.u,S)),qLower=ep(F(99,100)),
                     qUpper=ep(F(101,100)),qPoint=ep(F(1)))
    lines = ['import SparseLowerTail.Section08.FamilyExteriorLeaf',
             'import SparseLowerTail.Section08.FamilyParameterSmoke','',
             '/-! One checked exterior Taylor box. Not a complete cover. -/',
             'namespace SparseLowerTail.Certificate.FamilyExteriorSmoke',
             'open Numerics FamilyCoeff','set_option maxRecDepth 100000',
             'set_option maxHeartbeats 8000000','']
    for name,e in endpoints.items():
        q,n,l,u,lb,ub = e
        lines += [f'def {name} : ExpEndpointCertificate :=',
                  f'  ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(lb)},{rat(ub)}⟩',
                  f'theorem {name}_valid : {name}.Valid := by decide +kernel']
    lines += ['def midpoint : FamilyParameterCertificate :=',
              f'  ⟨midLog,midLog,deltaLower,deltaUpper,{delta.lean()}⟩',
              'theorem midpoint_valid : midpoint.Valid := by',
              '  refine ⟨midLog_valid,midLog_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩',
              '  all_goals decide +kernel','']
    with tempfile.TemporaryDirectory(prefix='family-exterior-') as directory:
        source = Path(directory)/'Propose.lean'
        source.write_text('\n'.join(lines)+'''
#eval (List.range 3).map fun n => (List.finRange 7).map fun i =>
  (derivativeExpr i n).dyadicEval midpoint.parameterBox
end SparseLowerTail.Certificate.FamilyExteriorSmoke
''')
        result = subprocess.run(['lake','env','lean',str(source)],cwd=ROOT,
                                text=True,capture_output=True,check=True)
    pairs = re.findall(r'lower := (-?\d+), upper := (-?\d+)',result.stdout)
    if len(pairs)!=21 or 'none' in result.stdout:
        raise ValueError('Expected 21 successful derivative interval proposals')
    rows = ['!['+','.join('⟨'+a+','+b+'⟩' for a,b in pairs[j:j+7])+']'
            for j in range(0,21,7)]
    lines += ['def centerD : Fin 3 → Fin 7 → DyadicInterval :=',
              '  !['+',\n    '.join(rows)+']',
              'theorem centerD_checked (n : Fin 3) (i : Fin 7) :',
              '    (derivativeExpr i n.val).dyadicEval midpoint.parameterBox=some (centerD n i) := by',
              '  fin_cases n <;> fin_cases i <;> decide +kernel','',
              'def data : FamilyTaylorData :=',
              '  ⟨FamilyScaledSmoke.Leaf0.parameter,midpoint,fun _ => qPoint,',
              '    FamilyParameterSmoke.intervals,centerD,7/1280⟩',
              'theorem data_valid : data.Valid := by',
              '  refine {',
              '    whole_valid := FamilyScaledSmoke.Leaf0.parameter_valid,',
              '    midpoint_valid := midpoint_valid, q_valid := fun _ => qPoint_valid,',
              '    whole_checked := FamilyParameterSmoke.intervals_checked,',
              '    center_checked := centerD_checked, point := rfl,',
              '    positive := ?_, center_lower := ?_, center_upper := ?_,',
              '    width_nonneg := ?_, width_left := ?_, width_right := ?_ }',
              '  all_goals decide +kernel','',
              'def box : FamilyBoxCertificate :=',
              '  ⟨FamilyScaledSmoke.Leaf0.parameter,FamilyScaledSmoke.Leaf0.box.coefficient,',
              '    fun _ => qLower,fun _ => qUpper⟩',
              'theorem box_valid : box.Valid :=',
              '  ⟨FamilyScaledSmoke.Leaf0.parameter_valid,FamilyScaledSmoke.Leaf0.box_valid.2.1,',
              '    fun _ => qLower_valid,fun _ => qUpper_valid⟩','',
              'def leaf : FamilyExteriorLeaf :=',
              '  ⟨data,box,fun _ => 1/100,fun i =>',
              '    -data.gradientUpper i*(1/100)+',
              '      min 0 (box.factoredHessianIntervals i i).toRational.lower*(1/100)^2/2⟩',
              'theorem leaf_valid : leaf.Valid := by',
              '  refine {',
              '    data_valid := data_valid, box_valid := box_valid,',
              '    same_parameter := rfl, choice := fun _ => Or.inl le_rfl,',
              '    center_lower := ?_, center_upper := ?_, radius_left := ?_,',
              '    radius_right := ?_, positive_margin := ?_ }',
              '  all_goals decide +kernel','',
              'theorem margin_bound : (1/1000 : ℚ)<leaf.margin := by decide +kernel','',
              'theorem positive {t : ℝ} (ht : Bounds t (39/10) (2503/640))',
              '    {q : FamilyVector} (hq : ∀i,Bounds (q i) (99/100) (101/100)) :',
              '    0<familyPhi (Real.exp (-t)) q := by',
              '  apply leaf.positive leaf_valid',
              '  · norm_num [leaf,data,FamilyScaledSmoke.Leaf0.parameter,',
              '      FamilyScaledSmoke.Leaf0.logLower,FamilyScaledSmoke.Leaf0.logUpper]',
              '    exact ht',
              '  · simpa [leaf,box,qLower,qUpper] using hq','',
              'end SparseLowerTail.Certificate.FamilyExteriorSmoke','']
    OUT.write_text('\n'.join(lines))
    print('Generated one exterior leaf, 21 proposed center derivatives; no coverage claim.')


if __name__=='__main__':
    main()
