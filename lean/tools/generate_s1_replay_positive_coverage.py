#!/usr/bin/env python3
"""Join separately kernel-checked S1 coverage and nonlinear leaf proofs.
The generator only writes proof terms; every reference and table entry is
validated by Lean. It does not trust the status JSON or proposal claims.
"""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'SparseLowerTail/Section05/S1Replay'

def pair(xs):
 if len(xs)==1:return xs[0]
 return '⟨'+pair(xs[::2])+','+pair(xs[1::2])+'⟩'
def pad(xs):return xs+['True.intro']*((1<<(len(xs)-1).bit_length())-len(xs))
def header(imports):return '\n'.join('import SparseLowerTail.Section05.S1Replay.'+i for i in imports)+'''\n\n/-! Combines checked exact geometry with checked nonlinear Taylor leaves. -/
namespace SparseLowerTail.Section05.S1Replay
open Numerics
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
'''
def generate(only=None):
 chunks=json.loads((ROOT/'data/s1-coverage-index.json').read_text())['chunks']
 ids=[i for c in chunks for i in c['leaves']]
 if ids != list(range(15280)):raise ValueError('Unexpected global leaf indexing')
 for c in chunks:
  k=c['chunk']
  if only is not None and k !=only:continue
  ns=f'PositiveCoverage{k:03d}';cov=f'Coverage{k:03d}'
  imports=[cov]+[f'Leaves{b:03d}'for b in sorted({i//128 for i in c['leaves']})]
  txt=header(imports)+f'\nnamespace {ns}\n'
  txt+=f'''theorem leaves_positive (Q : ℝ) :
    {cov}.leafTable.All (CoverBoxProperty Q
      (fun q => 0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q)) :=
  '''
  txt+=pair(pad([f'(fun _ hq _ => Batch{i//128:03d}.positive{i} hq)'for i in c['leaves']]))+'\n'
  txt+=f'''theorem positive {{Q : ℝ}} {{q : EdgeTriple}}
    (hq : q∈{cov}.initialBox.region) (horder : q∈orderedLogDomain Q) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q :=
  {cov}.covered (leaves_positive Q) q hq horder
end {ns}
end SparseLowerTail.Section05.S1Replay
'''
  (OUT/(ns+'.lean')).write_text(txt)
 if only is None:
  txt=header(['Coverage']+[f'PositiveCoverage{c["chunk"]:03d}'for c in chunks])
  txt+='\nnamespace PositiveCoverage\n'
  txt+='''theorem chunks_positive (Q : ℝ) :
    Coverage.chunkTable.All (CoverBoxProperty Q
      (fun q => 0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q)) :=
  '''+pair(pad([f'(fun _ hq hord => PositiveCoverage{c["chunk"]:03d}.positive hq hord)'for c in chunks]))+'\n'
  txt+='''theorem positive {Q : ℝ} {q : EdgeTriple}
    (hq : q∈Coverage.initialBox.region) (horder : q∈orderedLogDomain Q) :
    0 < logCertificate coverS1Theta coverS1Lam coverS1Vertex0 q :=
  Coverage.covered (chunks_positive Q) q hq horder
end PositiveCoverage
end SparseLowerTail.Section05.S1Replay
'''
  (OUT/'PositiveCoverage.lean').write_text(txt)
 print(f'{len(chunks)} positive coverage chunks; only={only}')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--only',type=int);a=p.parse_args();generate(a.only)
