#!/usr/bin/env python3
"""UNTRUSTED exact-dyadic arithmetic matching the exterior Lean expressions.

Floating-point values are never used for acceptance. Structural DAG sharing
only reuses identical expression results; Lean checks every accepted leaf.
"""
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
from generate_family_leaf_example import I, S, ep, expbox

ROOT = Path(__file__).resolve().parents[1]


class Program:
    def __init__(self,nodes,roots):
        self.nodes,self.roots = nodes,list(roots)
        needed=set()
        def visit(k):
            if k in needed:return
            needed.add(k)
            op,*args=nodes[k]
            if op in ('+','*'):
                visit(args[0]);visit(args[1])
            elif op in ('-','/'):
                visit(args[0])
            elif op not in ('r','v'):
                raise ValueError('Unknown DAG operation')
        for k in self.roots:visit(k)
        self.steps=[(k,nodes[k]) for k in sorted(needed)]
        self.constants={k:I(F(n[1],n[2])) for k,n in self.steps if n[0]=='r'}

    def __call__(self,box):
        values=[None]*len(self.nodes)
        for k,n in self.steps:
            op=n[0]
            if op=='r':v=self.constants[k]
            elif op=='v':v=box[n[1]]
            elif op=='+':v=values[n[1]]+values[n[2]]
            elif op=='*':v=values[n[1]]*values[n[2]]
            elif op=='-':v=-values[n[1]]
            elif op=='/':v=values[n[1]].inv()
            values[k]=v
        return [values[k] for k in self.roots]


def abs_upper(x):return F(max(-x.l,x.u),S)
def abs_lower(x):return F(max(0,x.l,-x.u),S)
def dot(a,b):return sum((x*y for x,y in zip(a,b)),I(0))


class Arithmetic:
    def __init__(self,path=ROOT/'data/family-expression-dag.json.gz'):
        payload=gzip.decompress(Path(path).read_bytes())
        self.payload_sha256=hashlib.sha256(payload).hexdigest()
        data=json.loads(payload)
        self.reference=data['reference_smoke']
        for name,digest in data['source_sha256'].items():
            if hashlib.sha256((ROOT/'SparseLowerTail'/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('Stale expression export: '+name)
        nodes,r=data['nodes'],data['roots']
        self.delta=Program(nodes,[r['delta']])
        self.derivatives=Program(nodes,[x for row in r['derivatives'] for x in row])
        self.weights=Program(nodes,r['weights'])
        self.gradient_weights=Program(nodes,[x for row in r['gradient_weights'] for x in row])
        self.hessian=Program(nodes,[x for row in r['hessian'] for x in row])

    @lru_cache(maxsize=32768)
    def endpoint(self,q):return ep(q)

    @lru_cache(maxsize=4096)
    def parameters(self,lo,hi):
        logI=I(I(lo).l,I(hi).u)
        z=expbox(self.endpoint(lo),self.endpoint(hi))
        delta=self.delta([z,logI,I(0)])[0]
        b=expbox(self.endpoint(F(delta.l,S)),self.endpoint(F(delta.u,S)))
        ds=self.derivatives([z,logI,b])
        return delta,[ds[j:j+7] for j in range(0,28,7)]

    def contact(self,lo,hi,delta):
        dl,du=F(delta.l,S),F(delta.u,S)
        qa=(lo[0]+dl,hi[0]+du);qb=(dl,du)
        for pattern,contacts in [('aaa',[qa]*3),('abb',[qa,qb,qb])]:
            if all(lo[i+1]>=u-F(1,10) and hi[i+1]<=l+F(1,10)
                   for i,(l,u) in enumerate(contacts)):
                return pattern
        return None

    def evaluate(self,lo,hi):
        """Exact box proposal. Sorted-domain pruning/coverage is separate."""
        mid=[(a+b)/2 for a,b in zip(lo,hi)]
        radii=[(b-a)/2 for a,b in zip(lo,hi)]
        try:
            delta,whole=self.parameters(lo[0],hi[0])
        except ValueError:
            return dict(kind='split',axis=0,reason='denominator')
        contact=self.contact(lo,hi,delta)
        if contact:return dict(kind=contact)
        try:
            _,center=self.parameters(mid[0],mid[0])
        except ValueError:
            return dict(kind='split',axis=0,reason='center-denominator')
        qs=mid[1:]
        xs=[expbox(self.endpoint(x),self.endpoint(x)) for x in qs]
        v=[I(x) for x in qs]+xs
        weights=self.weights(v)
        gradient_flat=self.gradient_weights(v)
        gweights=[gradient_flat[i:i+7] for i in range(0,21,7)]
        E=xs[0]*xs[1]*xs[2]
        phis=[dot(weights,center[n])+(E if n==0 else I(0)) for n in range(3)]
        third=dot(weights,whole[3])
        w=radii[0]
        Lerror=abs_upper(phis[1])*w+abs_upper(third)*w**3/6
        A=F(phis[0].l,S)-Lerror+min(F(0),F(phis[2].l,S))*w*w/2
        qbox=[I(I(a).l,I(b).u) for a,b in zip(lo[1:],hi[1:])]
        xbox=[expbox(self.endpoint(a),self.endpoint(b)) for a,b in zip(lo[1:],hi[1:])]
        hflat=self.hessian(qbox+xbox+whole[0])
        H=[hflat[i:i+3] for i in range(0,9,3)]
        plus,minus,beta,basebeta,choices,impacts=[],[],[],[],[],[Lerror]
        for i,r in enumerate(radii[1:]):
            g0=dot(gweights[i],center[0])-E
            g1=dot(gweights[i],center[1])
            g2=dot(gweights[i],whole[2])
            error=abs_upper(g1)*w+abs_upper(g2)*w*w/2
            P,m=abs_upper(g0)+error,abs_lower(g0)-error
            h=F(H[i][i].l,S)
            candidates=[(0,-P*r+min(F(0),h)*r*r/2)]
            if h>0:
                candidates.append((1,-P*P/(2*h)))
                if h*r<=m:candidates.append((2,-P*r+h*r*r/2))
            basebeta.append(candidates[0][1])
            choice,bv=max(candidates,key=lambda x:x[1])
            plus.append(P);minus.append(m);beta.append(bv);choices.append(choice)
            impacts.append(P*r+abs(h)*r*r/2)
        margin=A+sum(beta)
        base_margin=A+sum(basebeta)
        for i in range(3):
            for j in range(i+1,3):
                err=abs_upper(H[i][j])*radii[i+1]*radii[j+1]
                margin-=err;base_margin-=err;impacts[i+1]+=err;impacts[j+1]+=err
        result=dict(kind='taylor' if margin>0 else 'split',margin=margin,
                    baseline_margin=base_margin,value_lower=A,gradient_upper=plus,gradient_lower=minus,
                    choices=choices,beta=beta,axis=max(range(4),key=lambda i:impacts[i]))
        if radii[result['axis']]==0:result['axis']=max(range(4),key=lambda i:radii[i])
        return result
