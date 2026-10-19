#!/usr/bin/env python3
"""Generate full ABB Lean replay with shared parameters and endpoints.

Default: all leaves and their exact four-dimensional coverage. --smoke writes
one complete small subtree and selected end-region leaves, never the global
local-ABB theorem. Python proposes; every assertion is checked by Lean.
"""
import argparse
import gzip
import json
from fractions import Fraction as F
from pathlib import Path
from generate_exp_endpoints import rat, endpoint
from generate_family_leaf_example import I, S, expbox, coeff
from generate_s1_replay_coverage import Node, box, table, padded
from generate_s1_replay_positive_coverage import pair, pad

ROOT = Path(__file__).resolve().parents[1]
LEAF_BATCH = 32
ENDPOINT_BATCH = 64


def parse(data):
    if data.get('frontier') or data.get('scaled') is not True or data.get('factored',False):
        raise ValueError('Need a complete scaled proposal')
    if data['radius'] != '1/10':
        raise ValueError('Wrong radius')
    it = iter(data['preorder'])
    cursor = 0
    def go(lo, hi):
        nonlocal cursor
        code = next(it)
        if type(code) is not int or code not in range(5):
            raise ValueError('Invalid tree code')
        n = Node(lo, hi, code)
        if code == 0:
            row = data['leaves'][cursor]
            if list(map(F,row['lower'])) != lo or list(map(F,row['upper'])) != hi:
                raise ValueError('Leaf bounds disagree with exact midpoint tree')
            n.leaf, n.count = cursor, 1
            cursor += 1
        else:
            axis = code-1
            mid = (lo[axis]+hi[axis])/2
            lh, rl = hi.copy(),lo.copy()
            lh[axis] = rl[axis] = mid
            n.children = go(lo,lh),go(rl,hi)
            n.count = sum(c.count for c in n.children)
        return n
    root = go([F('3.9')]+[-F('.1')]*3,[F('9.5')]+[F('.1')]*3)
    if next(it,None) is not None or cursor != len(data['leaves']):
        raise ValueError('Extra tree codes or leaf records')
    return root


def ids(n):
    return [n.leaf] if n.code == 0 else ids(n.children[0])+ids(n.children[1])


def replay(n, mapping, stop=False):
    if stop and n.chunk >= 0:
        return f'(.leaf {n.chunk})'
    if n.code == 0:
        return f'(.leaf {mapping[n.leaf]})'
    return f'(.split {n.code-1} {replay(n.children[0],mapping,stop)} {replay(n.children[1],mapping,stop)})'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('proposal',type=Path)
    p.add_argument('--smoke',action='store_true')
    args = p.parse_args()
    raw = args.proposal.read_bytes()
    data = json.loads(gzip.decompress(raw) if args.proposal.suffix == '.gz' else raw)
    root = parse(data)
    chunks = []
    def cut(n):
        if n.count <= 32:
            n.chunk = len(chunks)
            chunks.append(n)
        else:
            for c in n.children:
                cut(c)
    cut(root)
    selected_chunks = [chunks[0]] if args.smoke else chunks
    selected = sorted(set(ids(chunks[0])+[len(data['leaves'])-1])) if args.smoke else list(range(len(data['leaves'])))
    ns = 'SparseLowerTail.Section08.FamilyABBReplay.'+('Smoke' if args.smoke else 'Full')
    out = ROOT/Path(ns.replace('.','/'))
    out.mkdir(parents=True,exist_ok=True)
    modules = []
    def header(imports):
        opens = 'open SparseLowerTail.Numerics'
        if imports != ['SparseLowerTail.Numerics.ExpEndpoints']:
            opens += '\nopen SparseLowerTail.Certificate SparseLowerTail.Section04'
        return '\n'.join('import '+i for i in imports)+f'''\n
/-! Generated untrusted proposals; all assertions require Lean kernel checks. -/
namespace {ns}
{opens}
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
    def save(name,text):
        (out/(name+'.lean')).write_text(text+f'\nend {ns}\n')
        modules.append(ns+'.'+name)
    parameters = {}
    for i in selected:
        row = data['leaves'][i]
        key = F(row['lower'][0]),F(row['upper'][0])
        if key not in parameters:
            lo,hi = key
            elo,ehi = endpoint(lo,20,60),endpoint(hi,20,60)
            L,z = I(I(lo).l,I(hi).u),expbox(elo,ehi)
            delta = 2*z*L/(1-z)**2
            dlo,dhi = F(delta.l,S),F(delta.u,S)
            cs = coeff(z,L,expbox(endpoint(dlo,20,60),endpoint(dhi,20,60)))
            parameters[key] = (len(parameters),delta,dlo,dhi,cs)
    values = set()
    leafvalues = {}
    for key,(_,_,dlo,dhi,_) in parameters.items():
        values.update([*key,dlo,dhi])
    for i in selected:
        row = data['leaves'][i]
        ql,qu = list(map(F,row['qLower'])),list(map(F,row['qUpper']))
        vals = ql+qu+[(q[a]+q[b])/2 for q in (ql,qu) for a in range(3) for b in range(a+1,3)]
        values.update(vals)
        leafvalues[i] = vals
    values = sorted(values)
    index = {q:i for i,q in enumerate(values)}
    def en(q):return f'exp{index[q]}'
    def emods(vals):return sorted({ns+f'.Endpoints{index[q]//ENDPOINT_BATCH:04d}' for q in vals})
    for batch in range((len(values)+ENDPOINT_BATCH-1)//ENDPOINT_BATCH):
        txt = header(['SparseLowerTail.Numerics.ExpEndpoints'])
        for q in values[batch*ENDPOINT_BATCH:(batch+1)*ENDPOINT_BATCH]:
            _,n,l,u,lb,ub = endpoint(q,20,60)
            txt += f'\ndef {en(q)} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(lb)},{rat(ub)}⟩\n'
            txt += f'theorem {en(q)}_valid : {en(q)}.Valid := by decide +kernel\n'
        save(f'Endpoints{batch:04d}',txt)
    for (lo,hi),(k,delta,dlo,dhi,cs) in parameters.items():
        txt = header(['SparseLowerTail.Section08.FamilyOffsetCover']+emods([lo,hi,dlo,dhi]))
        txt += f'\ndef parameter{k} : FamilyParameterCertificate := ⟨{en(lo)},{en(hi)},{en(dlo)},{en(dhi)},{delta.lean()}⟩\n'
        txt += f'theorem parameter{k}_valid : parameter{k}.Valid := by\n  refine ⟨{en(lo)}_valid,{en(hi)}_valid,{en(dlo)}_valid,{en(dhi)}_valid,?_,?_,?_⟩\n  all_goals decide +kernel\n'
        txt += f'def coefficients{k} : Fin 7 → DyadicInterval := !['+','.join(c.lean() for c in cs)+']\n'
        txt += f'theorem coefficients{k}_checked : ∀i,(FamilyCoeff.coefficientExpr i).dyadicEval parameter{k}.parameterBox=some (coefficients{k} i) := by\n  intro i; fin_cases i <;> decide +kernel\n'
        save(f'Parameter{k:04d}',txt)
    grouped = {}
    for i in selected:
        grouped.setdefault(i//LEAF_BATCH,[]).append(i)
    batches = sorted(grouped)
    for batch in batches:
        local = grouped[batch]
        pk = {parameters[(F(data['leaves'][i]['lower'][0]),F(data['leaves'][i]['upper'][0]))][0] for i in local}
        txt = header([ns+f'.Parameter{k:04d}' for k in sorted(pk)]+emods([q for i in local for q in leafvalues[i]]))
        for i in local:
            row = data['leaves'][i]
            lo,hi = list(map(F,row['lower'])),list(map(F,row['upper']))
            ql,qu = list(map(F,row['qLower'])),list(map(F,row['qUpper']))
            k = parameters[(lo[0],hi[0])][0]
            txt += f'\ndef offsetBox{i} : ReplayBox 4 := {box(Node(lo,hi,0))}\n'
            txt += f'def box{i} : FamilyBoxCertificate := ⟨parameter{k},coefficients{k},!['+','.join(en(q) for q in ql)+'],!['+','.join(en(q) for q in qu)+']⟩\n'
            txt += f'theorem box{i}_valid : box{i}.Valid := by\n  refine ⟨parameter{k}_valid,coefficients{k}_checked,?_,?_⟩\n'
            for qs in [ql,qu]:
                txt += '  · intro j; fin_cases j\n'+''.join(f'    · exact {en(q)}_valid\n' for q in qs)
            pairs = []
            for qs in [ql,qu]:
                pairs.append('!['+','.join('!['+','.join(en(qs[a] if a == b else (qs[a]+qs[b])/2) for b in range(3))+']' for a in range(3))+']')
            txt += f'def certificate{i} : FamilyScaledBoxCertificate := ⟨box{i},{pairs[0]},{pairs[1]}⟩\n'
            txt += f'theorem certificate{i}_valid : certificate{i}.Valid := by\n  refine ⟨box{i}_valid,?_⟩\n  intro a b hab\n  fin_cases a <;> fin_cases b\n  all_goals first | exact (hab rfl).elim | skip\n'
            for a in range(3):
                for b in range(3):
                    if a != b:
                        txt += f'  · exact ⟨{en((ql[a]+ql[b])/2)}_valid,{en((qu[a]+qu[b])/2)}_valid,by decide +kernel,by decide +kernel⟩\n'
            txt += f'def transform{i} : FamilyRationalMatrix := !['+','.join('!['+','.join(rat(F(t)) for t in row)+']' for row in row['transform'])+']\n'
            txt += f'theorem margins{i} : FamilyIntervalPositive (familyIntervalCongruence certificate{i}.hessianIntervals transform{i}) := by decide +kernel\n'
            txt += f'theorem enclosure{i} : box{i}.EnclosesABBOffsets offsetBox{i} := by decide +kernel\n'
            txt += f'theorem conclusion{i} : ∀x,offsetBox{i}.Contains x → familyABBOffsetProperty x :=\n  certificate{i}.abb_offset_property certificate{i}_valid transform{i} margins{i} enclosure{i}\n'
        save(f'Leaves{batch:04d}',txt)
    for n in selected_chunks:
        k,local = n.chunk,ids(n)
        txt = header([ns+f'.Leaves{b:04d}' for b in sorted({i//LEAF_BATCH for i in local})])
        txt += f'\nnamespace Coverage{k:04d}\ndef initialBox : ReplayBox 4 := {box(n)}\n'
        txt += 'def leafTable : RegisterTree (Option (ReplayBox 4)) := '+table(padded([f'some offsetBox{i}' for i in local]))+'\n'
        txt += 'def subdivision : BoxReplay 4 := '+replay(n,{i:j for j,i in enumerate(local)})+'\n'
        txt += 'theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel\n'
        txt += 'theorem leaf_proofs : leafTable.All (ReplayBoxProperty familyABBOffsetProperty) := '+pair(pad([f'conclusion{i}' for i in local]))+'\n'
        txt += 'theorem covered : ∀x,initialBox.Contains x → familyABBOffsetProperty x :=\n  subdivision.sound_table leaf_proofs valid\n'
        txt += f'end Coverage{k:04d}\n'
        save(f'Coverage{k:04d}',txt)
    if args.smoke:
        save('CheckedSubtree',header([ns+f'.Coverage{n.chunk:04d}' for n in selected_chunks]+[ns+f'.Leaves{b:04d}' for b in batches]))
        final = ns+'.CheckedSubtree'
    else:
        txt = header([ns+f'.Coverage{n.chunk:04d}' for n in chunks])
        txt += '\ndef chunkTable : RegisterTree (Option (ReplayBox 4)) := '+table(padded([f'some Coverage{n.chunk:04d}.initialBox' for n in chunks]))+'\n'
        txt += 'def subdivision : BoxReplay 4 := '+replay(root,{},True)+'\n'
        txt += 'theorem valid : subdivision.Valid chunkTable.get familyABBInitialBox := by decide +kernel\n'
        txt += 'theorem chunk_proofs : chunkTable.All (ReplayBoxProperty familyABBOffsetProperty) := '+pair(pad([f'Coverage{n.chunk:04d}.covered' for n in chunks]))+'\n'
        txt += '''theorem local_nonnegative_and_unique_zero {z : ℝ} (hz : 0<z)
    (hL : Bounds (branchLog z) (39/10) (19/2))
    {q : FamilyVector} (hq : q∈familyCube (familyContactABB z) (1/10)) :
    0≤familyPhi z q ∧ (familyPhi z q=0 ↔ q=familyContactABB z) :=
  familyABB_local_of_table chunkTable subdivision valid chunk_proofs hz hL hq
'''
        save('FullNeighborhood',txt)
        final = ns+'.FullNeighborhood'
    report = {'trust_status':'Generated, not yet built or audited','mode':'smoke' if args.smoke else 'full',
              'leaves':len(selected),'parameters':len(parameters),'endpoints':len(values),
              'coverage_chunks':len(selected_chunks),'final_module':final,'modules':modules}
    (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'modules'}),flush=True)


if __name__ == '__main__':
    main()
