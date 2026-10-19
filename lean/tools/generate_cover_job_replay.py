#!/usr/bin/env python3
"""Generate kernel proofs for any complete nonapex subdivision proposal.

Default: a small set of leaf checks. --full writes every leaf, exact coverage,
and the actual ordered-domain positivity theorem for the indexed paper job.
Search success flags have no authority: Lean checks margins and coverage.
"""
import argparse
import gzip
import json
from fractions import Fraction as F
from pathlib import Path
from generate_exp_endpoints import endpoint, rat
from generate_s1_replay_coverage import Node, table, padded, tree, leaves, box
from generate_s1_replay_positive_coverage import pair, pad
from cover_job_arithmetic import Arithmetic

ROOT = Path(__file__).resolve().parents[1]
BATCH = 16
ENDPOINT_BATCH = 64


def parse(proposal):
    if proposal.get('frontier') or proposal.get('status') != 'complete proposal':
        raise ValueError('A full completed subdivision is required')
    codes = iter(proposal['preorder'])
    data = []

    def go(lo, hi):
        lo = [max(lo), max(lo[1:]), lo[2]]
        hi = [hi[0], min(hi[:2]), min(hi)]
        try:
            code = next(codes)
        except StopIteration as exc:
            raise ValueError('Truncated subdivision') from exc
        n = Node(lo, hi, code)
        if code in (5, 6, 7):
            axis = code-5
            mid = (lo[axis]+hi[axis])/2
            if not lo[axis] < mid < hi[axis]:
                raise ValueError('Degenerate split')
            lh, rl = hi.copy(), lo.copy()
            lh[axis] = rl[axis] = mid
            n.children = (go(lo, lh), go(rl, hi))
            n.count = sum(c.count for c in n.children)
        elif code in (2, 3):
            if any(l > u for l, u in zip(lo, hi)):
                raise ValueError('Positive leaf has inverted bounds')
            n.code, n.leaf, n.count = 2, len(data), 1
            data.append((lo, hi, code))
        elif code == 4:
            if not any(l > u for l, u in zip(lo, hi)):
                raise ValueError('False empty leaf')
        else:
            raise ValueError('Unknown leaf code')
        return n

    Q = F(proposal['Q'])
    if Q <= 0:
        raise ValueError('Nonpositive cutoff')
    root = go([F(0)]*3, [Q]*3)
    sentinel = object()
    if next(codes, sentinel) is not sentinel:
        raise ValueError('Trailing subdivision nodes')
    return root, data


def generate(proposal, full=False):
    a = Arithmetic()
    job = proposal['job']
    if type(job) is not int or not 0 <= job < 36:
        raise ValueError('Unknown job')
    if proposal['expression_sha256'] != a.sha256:
        raise ValueError('Expression export mismatch')
    if F(proposal['Q']) != F(a.jobs[job]['Q']):
        raise ValueError('Wrong job cutoff')
    root, data = parse(proposal)
    name = f'Job{job:02d}' + ('Full' if full else 'Smoke')
    ns = f'SparseLowerTail.Section05.CoverJobReplay.{name}'
    out = ROOT / 'SparseLowerTail/Section05/CoverJobReplay' / name
    out.mkdir(parents=True, exist_ok=True)
    conclusion = (f'0 < logCertificate (coverCellTheta (CoverGeometry.nonapexCell {job})) '
                  f'(CoverGeometry.cellLambda (CoverGeometry.nonapexCell {job})) '
                  f'(CoverGeometry.nonapexVertex {job}) q')

    def header(imports):
        return '\n'.join('import '+i for i in imports)+f'''\n
/-! Generated untrusted proposal. Every arithmetic and coverage claim is kernel checked. -/
namespace {ns}
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''

    def save(name, text):
        (out / (name+'.lean')).write_text(text+f'\nend {ns}\n')

    ids = list(range(len(data)))
    if not full:
        smoke_root = root
        while smoke_root.count > 4:
            smoke_root = smoke_root.children[0]
        chosen = {0, len(data)-1} | set(leaves(smoke_root))
        for kind in (2, 3):
            chosen.update(next(([i] for i, row in enumerate(data) if row[2] == kind), []))
        ids = sorted(chosen)
    vals = sorted({q for i in ids for q in data[i][0]+data[i][1]+
                   [(l+h)/2 for l, h in zip(*data[i][:2])]})
    index = {q: i for i, q in enumerate(vals)}
    for b in range((len(vals)+ENDPOINT_BATCH-1)//ENDPOINT_BATCH):
        text = header(['SparseLowerTail.Numerics.ExpEndpoints'])
        for k in range(b*ENDPOINT_BATCH, min(len(vals), (b+1)*ENDPOINT_BATCH)):
            q, n, l, u, el, eu = endpoint(vals[k], 20, 60)
            text += f'\ndef exp{k} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(el)},{rat(eu)}⟩\n'
            text += f'theorem exp{k}_valid : exp{k}.Valid := by decide +kernel\n'
        save(f'Endpoints{b:04d}', text)
    batches = sorted({i//BATCH for i in ids})
    for b in batches:
        selected = [i for i in ids if i//BATCH == b]
        endpoints = {index[q]//ENDPOINT_BATCH for i in selected for q in data[i][0]+data[i][1]+
                     [(l+h)/2 for l, h in zip(*data[i][:2])]}
        text = header(['SparseLowerTail.Section05.CoverRefinedJobTaylorBox']+
                      [ns+f'.Endpoints{k:04d}' for k in sorted(endpoints)])
        for i in selected:
            lo, hi, kind = data[i]
            numeric = a.evaluate(job, lo, hi)
            if numeric['code'] != kind:
                raise ValueError(f'Stale leaf {i}: arithmetic classification changed')
            text += f'\ndef box{i} : LogBox := {box(Node(lo,hi,2))}\n'
            mid = [(l+h)/2 for l, h in zip(lo, hi)]
            vectors = ['!['+','.join(f'exp{index[q]}' for q in arr)+']' for arr in (lo,hi,mid)]
            text += f'def data{i} : S1TaylorBoxData := ⟨box{i},'+','.join(vectors)+'⟩\n'
            for tag, arr in [('lower',lo), ('upper',hi), ('center',mid)]:
                text += f'theorem data{i}_{tag}_valid : ∀ j, (data{i}.{tag}Exp j).Valid := by\n  intro j\n  fin_cases j\n'
                text += ''.join(f'  · exact exp{index[q]}_valid\n' for q in arr)
            if kind == 2:
                text += f'''theorem margin{i} :
    0 < RefinedCover.S1TaylorBoxData.jobMargin data{i} {job} := by decide +kernel
theorem positive{i} {{q : EdgeTriple}} (hq : q ∈ box{i}.region) :
    {conclusion} :=
  RefinedCover.S1TaylorBoxData.job_positive data{i} {job}
    data{i}_lower_valid data{i}_upper_valid data{i}_center_valid
    (by decide +kernel) (by decide +kernel) (by decide +kernel) margin{i} hq
'''
            else:
                text += f'''theorem margin{i} : 0 < (apexCertificateExpr.dyadicEval
    (RefinedCover.nonapexBoxIntervals (RefinedCover.S1TaylorBoxData.jobWholeBox data{i}) {job})).lower := by
  decide +kernel
theorem positive{i} {{q : EdgeTriple}} (hq : q ∈ box{i}.region) :
    {conclusion} :=
  RefinedCover.nonapexBox_positive (RefinedCover.S1TaylorBoxData.jobWholeBox data{i})
    ⟨data{i}_lower_valid,data{i}_upper_valid⟩ {job} margin{i} (q := edgeCoordinate q) (by
      intro k
      fin_cases k
      · exact hq 0
      · exact hq 1
      · exact hq 2)
'''
        save(f'Leaves{b:05d}', text)
    if not full:
        save('CheckedLeaves', header([ns+f'.Leaves{b:05d}' for b in batches]))
    chunks = []

    def cut(n):
        if n.count <= 32:
            n.chunk = len(chunks)
            chunks.append(n)
        else:
            for c in n.children:
                cut(c)
    cut(root if full else smoke_root)
    for k, n in enumerate(chunks):
        local = leaves(n)
        # Empty-only subtrees have no positive table entries.
        entries = [f'some box{i}' for i in local] or ['none']
        proofs = [f'(fun _ hq _ => positive{i} hq)' for i in local] or ['True.intro']
        text = header(['SparseLowerTail.Section05.CoverReplayTable',
                       'SparseLowerTail.Section05.CoverRefinedJobTaylorBox']+
                      [ns+f'.Leaves{b:05d}' for b in sorted({i//BATCH for i in local})])
        text += f'\nnamespace Coverage{k:05d}\ndef initialBox : LogBox := {box(n)}\n'
        text += 'def leafTable : RegisterTree (Option LogBox) := '+table(padded(entries))+'\n'
        text += 'def subdivision : CoverReplayTree := '+tree(n,{i:j for j,i in enumerate(local)})+'\n'
        text += 'theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel\n'
        text += f'theorem leaf_proofs (Q : ℝ) : leafTable.All (CoverBoxProperty Q (fun q => {conclusion})) :=\n  '+pair(pad(proofs))+'\n'
        text += f'''theorem covered {{Q : ℝ}} : ∀ q ∈ initialBox.region,
    q ∈ orderedLogDomain Q → {conclusion} :=
  subdivision.sound_table (leaf_proofs Q) valid
end Coverage{k:05d}
'''
        save(f'Coverage{k:05d}', text)
    if not full:
        save('CheckedSubtree',header([ns+'.CheckedLeaves',ns+'.Coverage00000']))
        return dict(mode='smoke; checked leaves and one subtree, no full-domain theorem',
                    leaves=ids,module=ns+'.CheckedSubtree')
    text = header([ns+f'.Coverage{k:05d}' for k in range(len(chunks))])
    text += f'\ndef initialBox : LogBox := {box(root)}\n'
    text += 'def chunkTable : RegisterTree (Option LogBox) := '+table(padded([f'some Coverage{k:05d}.initialBox' for k in range(len(chunks))]))+'\n'
    text += 'def subdivision : CoverReplayTree := '+tree(root,{},True)+'\n'
    text += 'theorem valid : subdivision.Valid chunkTable.get initialBox := by decide +kernel\n'
    text += f'theorem chunk_proofs (Q : ℝ) : chunkTable.All (CoverBoxProperty Q (fun q => {conclusion})) :=\n  '
    text += pair(pad([f'(fun _ hq hord => Coverage{k:05d}.covered _ hq hord)' for k in range(len(chunks))]))+'\n'
    text += f'''theorem ordered {{q : EdgeTriple}}
    (hq : q ∈ orderedLogDomain (CoverGeometry.cellQ (CoverGeometry.nonapexCell {job}))) :
    {conclusion} := by
  have hc := orderedLogDomain_subset_cube _ hq
  apply subdivision.sound_table (chunk_proofs _) valid q ?_ hq
  intro i
  fin_cases i
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.2.1
  · simpa [initialBox,edgeCoordinate,CoverGeometry.cellQ,CoverGeometry.nonapexCell] using hc.2.2
'''
    save('Ordered',text)
    return dict(mode='full replay; pending Lean build and audit',leaves=len(data),chunks=len(chunks),module=ns+'.Ordered')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('proposal',type=Path)
    p.add_argument('--full',action='store_true')
    args = p.parse_args()
    proposal = json.loads(gzip.decompress(args.proposal.read_bytes()))
    print(json.dumps(generate(proposal,args.full)))


if __name__ == '__main__':
    main()
