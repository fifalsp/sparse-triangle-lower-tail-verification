#!/usr/bin/env python3
"""Generate named exact box data and checked shared exponential endpoints.
Geometry comes from an untrusted proposal; coverage and leaf inequalities still
require Lean proofs. No proposal status field is used as proof evidence.
"""
from pathlib import Path
from fractions import Fraction as F
from generate_exp_endpoints import endpoint,rat
import json
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'SparseLowerTail/Section05/S1Replay'
def boxes_from_proposal():
 p=json.loads((ROOT/'data/s1-horner-subdivision-proposal.json').read_text());Q=F(p['Q']);st=[([F(0)]*3,[Q]*3)];leaves=[]
 for code in p['preorder']:
  lo,hi=st.pop();lo=[max(lo),max(lo[1:]),lo[2]];hi=[hi[0],min(hi[:2]),min(hi)]
  if code>=5:
   ax=code-5;mid=(lo[ax]+hi[ax])/2;lh=hi.copy();rl=lo.copy();lh[ax]=rl[ax]=mid;st.extend([(rl,hi),(lo,lh)])
  elif code==2:leaves.append((lo,hi))
  elif code!=4:raise ValueError('Unexpected proposal leaf code')
 if st:raise ValueError('Incomplete geometry')
 return leaves

def main():
 leaves=boxes_from_proposal();OUT.mkdir(parents=True,exist_ok=True)
 chunks=[]
 for start in range(0,len(leaves),256):
  index=start//256;name=f'Boxes{index:03d}';chunks.append(name)
  lines=['import SparseLowerTail.Section05.LogBoxSubdivision','',
   '/-! Exact rational box data only. Positivity and coverage are separate theorems. -/',
   'namespace SparseLowerTail.Section05.S1Replay','']
  for n in range(start,min(start+256,len(leaves))):
   lo,hi=leaves[n]
   lines+=[f'def box{n} : LogBox := ⟨!['+','.join(map(rat,lo))+'],!['+','.join(map(rat,hi))+']⟩']
  lines+=['','end SparseLowerTail.Section05.S1Replay','']
  (OUT/(name+'.lean')).write_text('\n'.join(lines))
 (OUT/'Boxes.lean').write_text('\n'.join('import SparseLowerTail.Section05.S1Replay.'+name for name in chunks)+'\n')
 vals=sorted(set(q for lo,hi in leaves for q in lo+hi+[(a+b)/2 for a,b in zip(lo,hi)]))
 lines=['import SparseLowerTail.Numerics.ExpEndpoints','',
 '/-! Shared exponential enclosures. Every Valid assertion is kernel checked. -/',
 'namespace SparseLowerTail.Section05.S1Replay','open Numerics',
 'set_option maxRecDepth 100000','set_option maxHeartbeats 4000000','']
 for i,q in enumerate(vals):
  qq,n,l,u,L,U=endpoint(q,20,60)
  lines += [f'def exp{i} : ExpEndpointCertificate :=',f'  ⟨{rat(qq)},{n},{rat(l)},{rat(u)},{rat(L)},{rat(U)}⟩',f'theorem exp{i}_valid : exp{i}.Valid := by decide +kernel','']
 lines+=['end SparseLowerTail.Section05.S1Replay','']
 (OUT/'Endpoints.lean').write_text('\n'.join(lines))
 (ROOT/'data/s1-replay-index.json').write_text(json.dumps({'trust_status':'Index data only, not a mathematical certificate','leaf_order':'preorder positive leaves; code2; exactly tightened rational boxes','box_chunk_size':256,'leaf_count':len(leaves),'endpoint_arguments':list(map(str,vals))},indent=2)+'\n')
 print(f'{len(leaves)} boxes in{len(chunks)} modules; {len(vals)} shared endpoints')
if __name__=='__main__':main()
