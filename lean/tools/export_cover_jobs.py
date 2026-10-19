#!/usr/bin/env python3
"""Export actual nonapex expressions as an untrusted, structurally shared DAG."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
SOURCES=['Numerics/IntervalExpr.lean','Numerics/PolynomialSimplify.lean','Numerics/DyadicInterval.lean','Numerics/DyadicTaylorFactored.lean','Numerics/ExpEndpoints.lean',
 'Section05/ApexExpr.lean','Section05/ApexCalculus.lean','Section05/CoverGenericTaylor.lean','Section05/CoverRefinedJobIntervals.lean',
 'Section05/CoverCoefficientData.lean','Section05/ApexRefinedPrimitives.lean',
 'Section05/ApexRefinedFanIntervals.lean','Section05/ApexRefinedSystem.lean']


def main():
    with tempfile.TemporaryFile(mode='w+') as output:
        result=subprocess.run(['lake','env','lean','tools/ExportCoverJobs.lean'],cwd=ROOT,
                              text=True,stdout=output,stderr=subprocess.STDOUT)
        output.seek(0);raw_text=output.read()
    if result.returncode:
        raise RuntimeError(raw_text)
    data=dict(gradient=[None]*3,hessian=[[None]*3 for _ in range(3)],jobs=[])
    for line in raw_text.splitlines():
        item=json.loads(line)
        if 'value' in item:data['value']=item['value']
        elif 'gradient_index' in item:data['gradient'][item['gradient_index']]=item['expr']
        elif 'hessian_indices' in item:
            i,j=item['hessian_indices'];data['hessian'][i][j]=item['expr']
        else:data['jobs'].append(item['job'])
    if len(data['jobs'])!=36:raise ValueError('Incomplete job export')
    nodes=[];seen={}
    def intern(e):
        op=e[0]
        if op in ('r','v'):key=tuple(e)
        elif op in ('+','*'):key=(op,intern(e[1]),intern(e[2]))
        elif op=='-':key=(op,intern(e[1]))
        else:raise ValueError('Unknown operation')
        if key not in seen:seen[key]=len(nodes);nodes.append(key)
        return seen[key]
    roots=dict(value=intern(data['value']),gradient=[intern(e) for e in data['gradient']],
               hessian=[[intern(e) for e in row] for row in data['hessian']])
    cover=json.loads((ROOT.parent/'data/cover.json').read_text())['cells']
    names=['F1','F2','F3','F4','F5','F6','S1','S2','S3','R1','B1','B2']
    for job in data['jobs']:
        name=names[job['cell']];job['cell_name']=name;job['Q']=cover[name]['Q']
    out=dict(schema=1,trust_status='UNTRUSTED search input; all boxes and coverage require Lean',
             nodes=nodes,roots=roots,jobs=data['jobs'],
             source_sha256={x:hashlib.sha256((ROOT/'SparseLowerTail'/x).read_bytes()).hexdigest() for x in SOURCES},
             cover_sha256=hashlib.sha256((ROOT.parent/'data/cover.json').read_bytes()).hexdigest())
    payload=(json.dumps(out,separators=(',',':'),sort_keys=True)+'\n').encode()
    dest=ROOT/'data/cover-job-expression-dag.json.gz';dest.write_bytes(gzip.compress(payload,mtime=0))
    print(json.dumps(dict(nodes=len(nodes),jobs=len(data['jobs']),compressed_bytes=dest.stat().st_size,
                         sha256=hashlib.sha256(payload).hexdigest())))


if __name__=='__main__':main()
