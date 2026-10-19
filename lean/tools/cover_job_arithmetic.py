#!/usr/bin/env python3
"""Untrusted exact-dyadic evaluation of the exported Lean nonapex jobs."""
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
from family_exterior_arithmetic import Program
from generate_family_leaf_example import I,S,ep,expbox

ROOT=Path(__file__).resolve().parents[1]


class Arithmetic:
    def __init__(self,path=ROOT/'data/cover-job-expression-dag.json.gz'):
        payload=gzip.decompress(Path(path).read_bytes());d=json.loads(payload)
        self.sha256=hashlib.sha256(payload).hexdigest();self.jobs=d['jobs']
        for name,digest in d['source_sha256'].items():
            if hashlib.sha256((ROOT/'SparseLowerTail'/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('Stale expression export: '+name)
        if hashlib.sha256((ROOT.parent/'data/cover.json').read_bytes()).hexdigest()!=d['cover_sha256']:
            raise ValueError('Cover source changed')
        r=d['roots'];self.value=Program(d['nodes'],[r['value']])
        self.center=Program(d['nodes'],[r['value']]+r['gradient'])
        self.hessian=Program(d['nodes'],[e for row in r['hessian'] for e in row])
        self.fixed=[[I(*x) for x in j['constants']+j['coefficients']+[j['lambda']]] for j in self.jobs]

    @lru_cache(maxsize=65536)
    def endpoint(self,q):return ep(q)

    def environment(self,job,lo,hi):
        return ([I(I(a).l,I(b).u) for a,b in zip(lo,hi)]+
                [expbox(self.endpoint(a),self.endpoint(b)) for a,b in zip(lo,hi)]+self.fixed[job])

    def evaluate(self,job,lo,hi):
        whole=self.environment(job,lo,hi);direct=self.value(whole)[0]
        if direct.l>0:return dict(code=3,margin=direct.l)
        mid=[(a+b)/2 for a,b in zip(lo,hi)]
        radii=[(b-a)/2 for a,b in zip(lo,hi)]
        velocity=[I(I(-r).l,I(r).u) for r in radii]
        value,*gradient=self.center(self.environment(job,mid,mid))
        first=sum((v*g for v,g in zip(velocity,gradient)),I(0))
        hessian=self.hessian(whole);second=I(0)
        for k,h in enumerate(hessian):
            i,j=divmod(k,3);vi,vj=velocity[i],velocity[j]
            prod=I(0,-(-max(vi.l**2,vi.u**2)//S)) if i==j else vi*vj
            second+=prod*h
        margin=2*value.l+2*first.l+second.l
        return dict(code=2 if margin>0 else None,margin=margin)

    def check_reference(self):
        for j in self.jobs:
            actual=self.value(self.environment(j['index'],[F(0)]*3,[F(1,512)]*3))[0]
            if [actual.l,actual.u]!=j['near_one_reference']:
                raise ValueError('Lean reference interval mismatch for job '+str(j['index']))
        return len(self.jobs)
