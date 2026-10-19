#!/usr/bin/env python3
"""Generate Lean proofs from an UNTRUSTED complete apex subdivision proposal.

The full mode generates all leaves, exact tree coverage, and the whole-cube
nonnegativity/zero-pattern implication. --smoke writes only representative
leaf checks; it deliberately generates no global theorem.
"""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from generate_exp_endpoints import endpoint, rat
from generate_s1_replay_coverage import Node, table, padded, tree, leaves, box
from generate_s1_replay_positive_coverage import pair, pad

ROOT = Path(__file__).resolve().parents[1]


def parse(proposal):
    iterator, leaf_data = iter(proposal['preorder']), []

    def go(lo, hi):
        lo, hi = [max(lo), max(lo[1:]), lo[2]], [hi[0], min(hi[:2]), min(hi)]
        code = next(iterator)
        n = Node(lo, hi, code)
        if code in (5, 6, 7):
            axis = code-5
            mid = (lo[axis]+hi[axis])/2
            lh, rl = hi.copy(), lo.copy()
            lh[axis] = rl[axis] = mid
            n.children = (go(lo, lh), go(rl, hi))
            n.count = sum(c.count for c in n.children)
        elif code in (0, 1, 2, 3):
            n.code, n.leaf, n.count = 2, len(leaf_data), 1
            leaf_data.append((lo, hi, code))
        elif code != 4:
            raise ValueError('Unknown leaf code')
        return n

    root = go([F(0)]*3, [F(proposal['Q'])]*3)
    if next(iterator, None) is not None:
        raise ValueError('Trailing proposal nodes')
    return root, leaf_data


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('proposal', type=Path)
    p.add_argument('--smoke', action='store_true')
    args = p.parse_args()
    proposal = json.loads(args.proposal.read_text())
    root, data = parse(proposal)
    fan = int(proposal['fan'])-1
    if not 0 <= fan < 6:
        raise ValueError('Fan index outside 1..6')
    name = f'F{fan+1}'+('Smoke' if args.smoke else '')
    ns = f'SparseLowerTail.Section05.ApexReplay.{name}'
    out = ROOT / 'SparseLowerTail/Section05/ApexReplay' / name
    out.mkdir(parents=True, exist_ok=True)

    def header(imports):
        return '\n'.join('import '+i for i in imports)+f'''\n
/-! Generated from untrusted proposal data. All assertions require kernel checks. -/
namespace {ns}
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''

    def save(name, text):
        (out / (name+'.lean')).write_text(text+f'\nend {ns}\n')

    ids = list(range(len(data)))
    if args.smoke:
        chosen = {0}
        for kind in (0, 1, 2, 3):
            matching = [i for i, row in enumerate(data) if row[2] == kind]
            if matching:
                chosen.add(matching[0])
                if matching[0] > 0:
                    chosen.add(matching[0]-1)
        ids = sorted(chosen)
    vals = sorted({q for i in ids if data[i][2] >= 2
                   for q in data[i][0]+data[i][1]+[(a+b)/2 for a, b in zip(*data[i][:2])]})
    index = {q: i for i, q in enumerate(vals)}
    text = header(['SparseLowerTail.Numerics.ExpEndpoints'])
    for i, q in enumerate(vals):
        qq, n, l, u, lower, upper = endpoint(q, 20, 60)
        text += f'\ndef exp{i} : ExpEndpointCertificate := ⟨{rat(qq)},{n},{rat(l)},{rat(u)},{rat(lower)},{rat(upper)}⟩\n'
        text += f'theorem exp{i}_valid : exp{i}.Valid := by decide +kernel\n'
    save('Endpoints', text)
    for b in sorted({i//256 for i in ids}):
        text = header(['SparseLowerTail.Section05.LogBoxSubdivision'])
        for i in ids:
            if i//256 == b:
                lo, hi, _ = data[i]
                text += f'\ndef box{i} : LogBox := '+box(Node(lo, hi, 2))+'\n'
        save(f'Boxes{b:03d}', text)
    batches = sorted({i//64 for i in ids})
    for b in batches:
        selected = [i for i in ids if i//64 == b]
        text = header([ns+'.Endpoints', 'SparseLowerTail.Section05.ApexCoverAssembly',
                       'SparseLowerTail.Section05.ApexRefinedTaylorBox'] +
                      [ns+f'.Boxes{k:03d}' for k in sorted({i//256 for i in selected})])
        for i in selected:
            lo, hi, kind = data[i]
            conclusion = f'ApexLeafConclusion {fan} q'
            if kind in (0, 1):
                text += f'''\ntheorem conclusion{i} {{q : EdgeTriple}} (hq : q ∈ box{i}.region) :
    {conclusion} :=
  box{i}.apexLeafConclusion_of_contact (mixed := {'true' if kind else 'false'})
    (by decide +kernel) hq
'''
                continue
            mid = [(a+b)/2 for a, b in zip(lo, hi)]
            vectors = ['!['+','.join(f'exp{index[q]}' for q in arr)+']' for arr in (lo, hi, mid)]
            text += f'\ndef data{i} : S1TaylorBoxData := ⟨box{i},'+','.join(vectors)+'⟩\n'
            for tag, arr in [('lower', lo), ('upper', hi), ('center', mid)]:
                text += f'theorem data{i}_{tag}_valid : ∀ j, (data{i}.{tag}Exp j).Valid := by\n  intro j\n  fin_cases j\n'
                text += ''.join(f'  · exact exp{index[q]}_valid\n' for q in arr)
            if kind == 2:
                text += f'''theorem margin{i} : 0 < data{i}.apexRefinedMargin {fan} := by decide +kernel
theorem conclusion{i} {{q : EdgeTriple}} (hq : q ∈ box{i}.region) :
    {conclusion} := by
  apply apexLeafConclusion_of_positive
  exact data{i}.apexRefined_positive {fan}
    data{i}_lower_valid data{i}_upper_valid data{i}_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin{i} hq
'''
            else:
                text += f'''theorem margin{i} :
    0 < (apexCertificateExpr.dyadicEval (apexRefinedBoxIntervals data{i}.jobWholeBox {fan})).lower := by
  decide +kernel
theorem conclusion{i} {{q : EdgeTriple}} (hq : q ∈ box{i}.region) :
    {conclusion} := by
  apply apexLeafConclusion_of_positive
  exact apexRefinedBox_positive data{i}.jobWholeBox
    ⟨data{i}_lower_valid, data{i}_upper_valid⟩ {fan} margin{i} hq
'''
        save(f'Leaves{b:03d}', text)
    if args.smoke:
        save('CheckedLeaves', header([ns+f'.Leaves{b:03d}' for b in batches]))
        print(json.dumps({'mode': 'smoke only', 'leaves': ids, 'module': ns+'.CheckedLeaves'}))
        return
    chunks = []

    def cut(n):
        if n.count <= 64:
            n.chunk = len(chunks)
            chunks.append(n)
        else:
            for c in n.children:
                cut(c)
    cut(root)
    for k, n in enumerate(chunks):
        local = leaves(n)
        text = header(['SparseLowerTail.Section05.CoverReplayTable']+
                      [ns+f'.Leaves{b:03d}' for b in sorted({i//64 for i in local})])
        text += f'\nnamespace Coverage{k:03d}\ndef initialBox : LogBox := {box(n)}\n'
        text += 'def leafTable : RegisterTree (Option LogBox) := '+table(padded([f'some box{i}' for i in local]))+'\n'
        text += 'def subdivision : CoverReplayTree := '+tree(n, {i: j for j, i in enumerate(local)})+'\n'
        text += 'theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel\n'
        text += f'theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (ApexLeafConclusion {fan})) :=\n  '
        text += pair(pad([f'(fun _ hq _ => conclusion{i} hq)' for i in local]))+'\n'
        text += f'''theorem covered {{Q : ℝ}} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → ApexLeafConclusion {fan} q :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage{k:03d}
'''
        save(f'Coverage{k:03d}', text)
    text = header([ns+f'.Coverage{k:03d}' for k in range(len(chunks))])
    text += f'\ndef initialBox : LogBox := {box(root)}\n'
    text += 'def chunkTable : RegisterTree (Option LogBox) := '+table(padded([f'some Coverage{k:03d}.initialBox' for k in range(len(chunks))]))+'\n'
    text += 'def subdivision : CoverReplayTree := '+tree(root, {}, True)+'\n'
    text += 'theorem valid : subdivision.Valid chunkTable.get initialBox := by decide +kernel\n'
    text += f'theorem chunk_proofs (Q : ℝ) : chunkTable.All (CoverBoxProperty Q (ApexLeafConclusion {fan})) :=\n  '
    text += pair(pad([f'(fun _ hq hord => Coverage{k:03d}.covered _ hq hord)' for k in range(len(chunks))]))+'\n'
    text += f'''theorem ordered {{q : EdgeTriple}}
    (hq : q ∈ orderedLogDomain (CoverGeometry.cellQ (({fan} : Fin 6).castAdd 6))) : ApexLeafConclusion {fan} q := by
  have hc := orderedLogDomain_subset_cube _ hq
  apply subdivision.sound_table (chunk_proofs _) valid q ?_ hq
  intro j
  fin_cases j
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ] using hc.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ] using hc.2.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ] using hc.2.2

theorem full_cube : ∀ u ∈ edgeCube (Real.exp (-CoverGeometry.cellQ (({fan} : Fin 6).castAdd 6))),
    0 ≤ coverCertificate (apexFanTheta {fan}) (CoverGeometry.cellLambda (({fan} : Fin 6).castAdd 6)) u criticalPoint ∧
    (coverCertificate (apexFanTheta {fan}) (CoverGeometry.cellLambda (({fan} : Fin 6).castAdd 6)) u criticalPoint = 0 →
      u ∈ criticalPatterns) :=
  apex_nonneg_patterns_of_ordered {fan} _ (fun _ hq => ordered hq)
'''
    save('FullCube', text)
    print(json.dumps({'mode': 'full proposal replay', 'leaves': len(data), 'chunks': len(chunks), 'module': ns+'.FullCube'}))


if __name__ == '__main__':
    main()
