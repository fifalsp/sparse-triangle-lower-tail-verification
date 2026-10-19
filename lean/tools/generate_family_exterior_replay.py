#!/usr/bin/env python3
"""Generate compact-family replay; numerical assertions require Lean checks.

Default is a small representative smoke target. --full writes the entire
proposal and is intended for the cluster. The full result still explicitly
requires FamilyABBLocal; it never promotes that internal premise to an axiom.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
from family_exterior_arithmetic import Arithmetic, S
from propose_family_exterior_cover import INITIAL
from generate_exp_endpoints import rat
from generate_s1_replay_coverage import Node, box, table, padded
from generate_s1_replay_positive_coverage import pair, pad
from generate_family_abb_replay import ids, replay

ROOT=Path(__file__).resolve().parents[1]
BATCH=16
EP_BATCH=64


def parse(data):
    if data['frontier'] or tuple(list(map(F,x)) for x in data['initial'])!=INITIAL:
        raise ValueError('Need a complete proposal on the exact compact domain')
    it=iter(data['tree']);seen=set()
    def go(lo,hi):
        code=next(it)
        if type(code) is not int:raise ValueError('Invalid node code')
        n=Node(lo,hi,0 if code<0 else code+1)
        if code<0:
            k=-code-1
            if k in seen or not 0<=k<len(data['leaves']):raise ValueError('Invalid leaf reference')
            seen.add(k);row=data['leaves'][k]
            if (list(map(F,row['lower'])),list(map(F,row['upper'])))!=(lo,hi):
                raise ValueError('Leaf differs from exact midpoint tree')
            if row['kind'] not in ('taylor','aaa','abb','ordered-empty'):
                raise ValueError('Unknown leaf kind')
            n.leaf,n.count=k,1
        else:
            if code not in range(4):raise ValueError('Invalid split axis')
            mid=(lo[code]+hi[code])/2
            if not lo[code]<mid<hi[code]:raise ValueError('Degenerate split')
            lh,rl=hi.copy(),lo.copy();lh[code]=rl[code]=mid
            n.children=go(lo,lh),go(rl,hi)
            n.count=sum(c.count for c in n.children)
        return n
    root=go(*INITIAL)
    if next(it,None) is not None or len(seen)!=len(data['leaves']):
        raise ValueError('Extra or unused data')
    return root


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('proposal',type=Path)
    p.add_argument('--full',action='store_true')
    args=p.parse_args()
    payload=gzip.decompress(args.proposal.read_bytes());data=json.loads(payload)
    a=Arithmetic()
    if data['expression_sha256']!=a.payload_sha256:raise ValueError('Expression bundle changed')
    root=parse(data);chunks=[]
    def cut(n):
        if n.count<=BATCH:n.chunk=len(chunks);chunks.append(n)
        else:
            for c in n.children:cut(c)
    cut(root)
    if args.full:
        selected=list(range(len(data['leaves'])));selected_chunks=chunks
    else:
        chosen=set(ids(chunks[0]));kinds=set();candidates=set()
        for i,row in enumerate(data['leaves']):
            if row['kind'] not in kinds:
                chosen.add(i);kinds.add(row['kind'])
            if row['kind']=='taylor' and set(row['choices'])-candidates:
                chosen.add(i);candidates.update(row['choices'])
        selected=sorted(chosen);selected_chunks=chunks[:1]
    ns='SparseLowerTail.Section08.FamilyExteriorReplay.'+('Full' if args.full else 'Smoke')
    out=ROOT/Path(ns.replace('.','/'));out.mkdir(parents=True,exist_ok=True)
    modules=[]
    def header(imports):
        opens='open SparseLowerTail.Numerics'
        if imports!=['SparseLowerTail.Numerics.ExpEndpoints']:
            opens+=' SparseLowerTail.Certificate'
        return '\n'.join('import '+s for s in imports)+f'''

/-! Generated proposal data. Every theorem must pass the Lean kernel.
The full ABB neighborhood remains an explicit internal premise. -/
namespace {ns}
{opens}
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
    def save(name,text):
        (out/(name+'.lean')).write_text(text+f'\nend {ns}\n')
        modules.append(ns+'.'+name)
    params={};values=set();leafvals={}
    for i in selected:
        row=data['leaves'][i];lo,hi=list(map(F,row['lower'])),list(map(F,row['upper']))
        if row['kind']=='ordered-empty':
            if not(hi[1]<lo[2] or hi[2]<lo[3]):raise ValueError('Invalid ordered-empty leaf')
            continue
        result=a.evaluate(lo,hi)
        if result['kind']!=row['kind']:raise ValueError('Leaf acceptance changed')
        if row['kind']=='taylor' and (F(row['margin'])!=result['margin'] or
                list(map(F,row['beta']))!=result['beta'] or row['choices']!=result['choices']):
            raise ValueError('Taylor numerical proposal changed')
        mid=[(x+y)/2 for x,y in zip(lo,hi)]
        keys=[(lo[0],hi[0])]+([(mid[0],mid[0])] if row['kind']=='taylor' else [])
        for key in keys:
            if key not in params:
                delta,ds=a.parameters(*key);dl,du=F(delta.l,S),F(delta.u,S)
                params[key]=(len(params),delta,ds,dl,du)
                values.update([*key,dl,du])
        if row['kind']=='taylor':
            leafvals[i]=lo[1:]+hi[1:]+mid[1:];values.update(leafvals[i])
    values=sorted(values);index={q:i for i,q in enumerate(values)}
    def en(q):return f'exp{index[q]}'
    def emods(vs):return sorted({ns+f'.Endpoints{index[q]//EP_BATCH:04d}' for q in vs})
    def vec(vs):return '!['+','.join(vs)+']'
    for batch in range((len(values)+EP_BATCH-1)//EP_BATCH):
        txt=header(['SparseLowerTail.Numerics.ExpEndpoints'])
        for q in values[batch*EP_BATCH:(batch+1)*EP_BATCH]:
            _,n,l,u,lb,ub=a.endpoint(q)
            txt+=f'\ndef {en(q)} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(lb)},{rat(ub)}⟩\n'
            txt+=f'theorem {en(q)}_valid : {en(q)}.Valid := by decide +kernel\n'
        save(f'Endpoints{batch:04d}',txt)
    for (lo,hi),(k,delta,ds,dl,du) in params.items():
        txt=header(['SparseLowerTail.Section08.FamilyCompactReplay']+emods([lo,hi,dl,du]))
        txt+=f'\ndef parameter{k} : FamilyParameterCertificate := ⟨{en(lo)},{en(hi)},{en(dl)},{en(du)},{delta.lean()}⟩\n'
        txt+=f'theorem parameter{k}_valid : parameter{k}.Valid := by\n  refine ⟨{en(lo)}_valid,{en(hi)}_valid,{en(dl)}_valid,{en(du)}_valid,?_,?_,?_⟩\n  all_goals decide +kernel\n'
        txt+=f'def derivatives{k} : Fin 4 → Fin 7 → DyadicInterval := '+vec([vec([v.lean() for v in row]) for row in ds])+'\n'
        txt+=f'theorem derivatives{k}_checked (n : Fin 4) (i : Fin 7) :\n    (FamilyCoeff.derivativeExpr i n.val).dyadicEval parameter{k}.parameterBox=some (derivatives{k} n i) := by\n  fin_cases n <;> fin_cases i <;> decide +kernel\n'
        save(f'Parameter{k:04d}',txt)
    grouped={}
    for i in selected:grouped.setdefault(i//BATCH,[]).append(i)
    for batch,local in sorted(grouped.items()):
        keys=set();eps=[]
        for i in local:
            row=data['leaves'][i];lo,hi=list(map(F,row['lower'])),list(map(F,row['upper']))
            if row['kind']!='ordered-empty':keys.add((lo[0],hi[0]))
            if row['kind']=='taylor':
                mid=(lo[0]+hi[0])/2;keys.add((mid,mid));eps+=leafvals[i]
        imports=['SparseLowerTail.Section08.FamilyCompactReplay']+[ns+f'.Parameter{params[key][0]:04d}' for key in sorted(keys)]+emods(eps)
        txt=header(imports)
        for i in local:
            row=data['leaves'][i];kind=row['kind']
            lo,hi=list(map(F,row['lower'])),list(map(F,row['upper']))
            txt+=f'\ndef domain{i} : ReplayBox 4 := {box(Node(lo,hi,0))}\n'
            if kind=='ordered-empty':
                txt+=f'theorem conclusion{i} (_hABB : FamilyABBLocal) : ∀x,domain{i}.Contains x → familyCompactProperty x :=\n  familyCompactProperty_ordered_empty domain{i} (by decide +kernel)\n'
                continue
            k=params[(lo[0],hi[0])][0]
            if kind in ('aaa','abb'):
                mixed='true' if kind=='abb' else 'false'
                txt+=f'theorem conclusion{i} (hABB : FamilyABBLocal) : ∀x,domain{i}.Contains x → familyCompactProperty x :=\n  parameter{k}.compact_property_of_contact hABB parameter{k}_valid {mixed} (by decide +kernel)\n'
                continue
            mid=[(x+y)/2 for x,y in zip(lo,hi)];c=params[(mid[0],mid[0])][0]
            txt+=f'def data{i} : FamilyTaylorData :=\n  ⟨parameter{k},parameter{c},{vec([en(q) for q in mid[1:]])},derivatives{k},fun n => derivatives{c} n.castSucc,{rat((hi[0]-lo[0])/2)}⟩\n'
            txt+=f'theorem data{i}_valid : data{i}.Valid := by\n  refine {{\n    whole_valid := parameter{k}_valid, midpoint_valid := parameter{c}_valid,\n    whole_checked := derivatives{k}_checked, center_checked := fun n => derivatives{c}_checked n.castSucc,\n    q_valid := ?_, point := rfl, positive := ?_, center_lower := ?_, center_upper := ?_,\n    width_nonneg := ?_, width_left := ?_, width_right := ?_ }}\n'
            txt+='  · intro j; fin_cases j\n'+''.join(f'    · exact {en(q)}_valid\n' for q in mid[1:])
            txt+='  all_goals decide +kernel\n'
            txt+=f'def box{i} : FamilyBoxCertificate := ⟨parameter{k},derivatives{k} 0,{vec([en(q) for q in lo[1:]])},{vec([en(q) for q in hi[1:]])}⟩\n'
            txt+=f'theorem box{i}_valid : box{i}.Valid := by\n  refine ⟨parameter{k}_valid,derivatives{k}_checked 0,?_,?_⟩\n'
            for qs in [lo[1:],hi[1:]]:
                txt+='  · intro j; fin_cases j\n'+''.join(f'    · exact {en(q)}_valid\n' for q in qs)
            txt+=f'def leaf{i} : FamilyExteriorLeaf := ⟨data{i},box{i},{vec([rat((y-x)/2) for x,y in zip(lo[1:],hi[1:])])},{vec([rat(F(v)) for v in row["beta"]])}⟩\n'
            txt+=f'theorem leaf{i}_valid : leaf{i}.Valid := by\n  refine {{\n    data_valid := data{i}_valid, box_valid := box{i}_valid,\n    same_parameter := rfl, center_lower := ?_, center_upper := ?_,\n    radius_left := ?_, radius_right := ?_, choice := ?_, positive_margin := ?_ }}\n  all_goals decide +kernel\n'
            txt+=f'theorem conclusion{i} (_hABB : FamilyABBLocal) : ∀x,domain{i}.Contains x → familyCompactProperty x :=\n  leaf{i}.compact_property leaf{i}_valid (by decide +kernel)\n'
        save(f'Leaves{batch:04d}',txt)
    for n in selected_chunks:
        k,local=n.chunk,ids(n)
        txt=header([ns+f'.Leaves{b:04d}' for b in sorted({i//BATCH for i in local})])
        txt+=f'\nnamespace Coverage{k:04d}\ndef initialBox : ReplayBox 4 := {box(n)}\n'
        txt+='def leafTable : RegisterTree (Option (ReplayBox 4)) := '+table(padded([f'some domain{i}' for i in local]))+'\n'
        txt+='def subdivision : BoxReplay 4 := '+replay(n,{i:j for j,i in enumerate(local)})+'\n'
        txt+='theorem valid : subdivision.Valid leafTable.get initialBox := by decide +kernel\n'
        txt+='theorem leaf_proofs (hABB : FamilyABBLocal) : leafTable.All (ReplayBoxProperty familyCompactProperty) := '+pair(pad([f'conclusion{i} hABB' for i in local]))+'\n'
        txt+='theorem covered (hABB : FamilyABBLocal) : ∀x,initialBox.Contains x → familyCompactProperty x :=\n  subdivision.sound_table (leaf_proofs hABB) valid\n'
        txt+=f'end Coverage{k:04d}\n';save(f'Coverage{k:04d}',txt)
    if args.full:
        txt=header([ns+f'.Coverage{n.chunk:04d}' for n in chunks])
        txt+='\ndef chunkTable : RegisterTree (Option (ReplayBox 4)) := '+table(padded([f'some Coverage{n.chunk:04d}.initialBox' for n in chunks]))+'\n'
        txt+='def subdivision : BoxReplay 4 := '+replay(root,{},True)+'\n'
        txt+='theorem valid : subdivision.Valid chunkTable.get familyCompactInitialBox := by decide +kernel\n'
        txt+='theorem chunk_proofs (hABB : FamilyABBLocal) : chunkTable.All (ReplayBoxProperty familyCompactProperty) := '+pair(pad([f'Coverage{n.chunk:04d}.covered hABB' for n in chunks]))+'\n'
        txt+='theorem compact_certificate (hABB : FamilyABBLocal) : SparseLowerTail.Section08.CompactFamilyCertificate :=\n  compactFamilyCertificate_of_table chunkTable subdivision valid (chunk_proofs hABB)\n'
        save('CompactCertificate',txt);final=ns+'.CompactCertificate'
    else:
        save('CheckedSubtree',header([ns+f'.Coverage{n.chunk:04d}' for n in selected_chunks]+[ns+f'.Leaves{b:04d}' for b in grouped]));final=ns+'.CheckedSubtree'
    report=dict(trust_status='Generated, not yet built or audited; ABB remains an internal premise',
                mode='full' if args.full else 'smoke',leaves=len(selected),parameters=len(params),endpoints=len(values),
                kinds=dict(Counter(data['leaves'][i]['kind'] for i in selected)),
                selected=selected,coverage_chunks=len(selected_chunks),final_module=final,modules=modules,
                proposal_sha256=hashlib.sha256(payload).hexdigest())
    (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('modules','selected')}),flush=True)


if __name__=='__main__':main()
