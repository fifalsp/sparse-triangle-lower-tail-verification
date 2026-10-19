"""New fail-closed Arb verifier for the inherited twelve-cell endpoint cover.

This reconstructs source specifications, rather than recovering its absent
original code. Covers exact binary64 input cubes with dyadic subdivision.
"""
from pathlib import Path
from fractions import Fraction as Q
import sys,json,time,hashlib,math
import numpy as np
import endpoint_common as ec
A,arb,ctx=ec.A,ec.arb,ec.ctx
HERE=Path(__file__).resolve().parent


def model(cellname):
    c=ec.setup_constants();cell=ec.input_data()[cellname];th,solve=ec.tangent_coefficients(cell,c)
    return c,cell,th,A(Q(cell['lam'])),solve


def eigen_proposal(H):
    mat=np.array([[float(z.mid()) for z in row] for row in H]);eig=np.linalg.eigvalsh(mat)[0]
    if eig<=0:return None
    return Q(math.floor(float(eig)*.9*10**16),10**16)


def third_sum(vals):
    indices=json.loads((HERE/'template_manifest.json').read_text())['indices'][10:]
    out=A(0)
    for idx,v in zip(indices,vals[10:]):
        mult=1 if len(set(idx))==1 else 3 if len(set(idx))==2 else 6
        out+=mult*abs(v)
    return out


def local_checks(c,cell,th,lam):
    assert cell['apex'];m,F=c['m'],c['F'];results=[]
    for pattern,rad in enumerate(cell['local_radii'],1):
        radius=Q(rad);center=[c['qa']]*3 if pattern==1 else[c['qa'],c['qb'],c['qb']]
        val=ec.evaluate(center,th,lam,c,m,F);H=ec.hessian(val);ell=eigen_proposal(H)
        assert ell is not None and ell>0
        Hshift=[[H[i][j]-(A(ell) if i==j else 0) for j in range(3)] for i in range(3)]
        assert ec.positive_definite(Hshift)
        wide=[z+arb(0,A(radius)) for z in center];vals=ec.evaluate(wide,th,lam,c,m,F)
        S3=third_sum(vals)
        # The published radii are part of the certificate inputs: never
        # silently replace a failed local check by a smaller neighborhood.
        assert A(radius)*S3<3*A(ell), ('Printed local radius fails',pattern,str(radius))
        results.append(dict(pattern=pattern,radius=str(radius),hessian_lower=str(ell),third_sum_upper=str(S3.upper()),
                            taylor_margin=str(3*A(ell)-A(radius)*S3)))
    return results


def inside_local(q,c,locals_):
    for item in locals_:
        pattern=item['pattern'];rad=A(Q(item['radius']))
        centers=[c['qa']]*3 if pattern==1 else[c['qa'],c['qb'],c['qb']]
        if all(abs(a-b)<rad for a,b in zip(q,centers)):return f'local{pattern}'
    return None


def box_intervals(lo,hi):return [ec.ball(l,h) for l,h in zip(lo,hi)]


def analyze(lo,hi,c,th,lam,m,F,target,locals_):
    q=box_intervals(lo,hi)
    if locals_:
        kind=inside_local(q,c,locals_)
        if kind:return kind,None
    direct=ec.evaluate(q,th,lam,c,m,F,'value')[0]
    if direct>target:return 'direct',str(direct.lower())
    mid=[(l+h)/2 for l,h in zip(lo,hi)]
    if any(not l<=mi<=h for l,mi,h in zip(lo,mid,hi)):raise AssertionError('Center outside box')
    ma=list(map(A,mid));r=[max(abs(A(l)-mi),abs(A(h)-mi)) for l,h,mi in zip(lo,hi,ma)]
    center=ec.evaluate(ma,th,lam,c,m,F)
    box=ec.evaluate(q,th,lam,c,m,F)
    H=ec.hessian(center);K=ec.hessian(box)
    first=center[0]-sum(abs(g)*rr for g,rr in zip(box[1:4],r))
    if first>target:return 'Taylor1',str(first.lower())
    second=center[0]-sum(abs(g)*rr for g,rr in zip(center[1:4],r))
    for i in range(3):
        if not K[i][i]>=0:second-=abs(K[i][i])*r[i]*r[i]/2
        for j in range(i+1,3):second-=abs(K[i][j])*r[i]*r[j]
    if second>target:return 'Taylor2',str(second.lower())
    if ec.positive_definite(H):
        try:
            hnum=np.array([[float(z.mid()) for z in row] for row in H]);gnum=np.array([float(z.mid()) for z in center[1:4]])
            y=-np.linalg.solve(hnum,gnum)
            y=np.clip(y,-np.array(list(map(float,r))),np.array(list(map(float,r))))
            if not np.all(np.isfinite(y)):return None,None
        except (ValueError,np.linalg.LinAlgError):return None,None
        ya=[A(Q(float(v))) for v in y]
        gy=[center[i+1]+sum(H[i][j]*ya[j] for j in range(3)) for i in range(3)]
        third=center[0]+sum(center[i+1]*ya[i] for i in range(3))
        third+=sum(ya[i]*H[i][j]*ya[j] for i in range(3) for j in range(3))/2
        for i in range(3):
            # Enclose the minimum over two endpoint affine expressions.
            aa=gy[i]*(-r[i]-ya[i]);bb=gy[i]*(r[i]-ya[i])
            third+=min(aa.lower(),bb.lower())
        third-=third_sum(box)*max(r)**3/6
        if third>target:return 'Taylor3',str(third.lower())
    return None,None


def verify_job(cellname,vertex,budget=2000000):
    start=time.monotonic();c,cell,th,lam,solve=model(cellname)
    support=ec.support_check(cell,c);locals_=[]
    if vertex=='apex':
        assert cell['apex'];m,F=c['m'],c['F'];target=3*A(Q(float('1e-12')))
        locals_=local_checks(c,cell,th,lam)
    else:
        i=int(vertex);m,F=map(lambda z:A(Q(z)),cell['vertices'][i]);target=3*A(Q(cell['targets'][i]))
    qmax=float(Q(cell['Q']));todo=[((0.,0.,0.),(qmax,qmax,qmax))]
    count=0;counts={};digest=hashlib.sha256();minima={};maxdepth=0;status='incomplete';failure=None
    try:
        while todo and count<budget:
            lo,hi=todo.pop();count+=1
            # Tighten only using necessary consequences of q0>=q1>=q2.
            lo=(max(lo[0],lo[1],lo[2]),max(lo[1],lo[2]),lo[2])
            hi=(hi[0],min(hi[0],hi[1]),min(hi[0],hi[1],hi[2]))
            if any(l>h for l,h in zip(lo,hi)):
                counts['empty']=counts.get('empty',0)+1;continue
            kind,lower=analyze(lo,hi,c,th,lam,m,F,target,locals_)
            if kind:
                counts[kind]=counts.get(kind,0)+1;digest.update(repr((kind,lo,hi)).encode())
                if lower is not None:
                    v=A(lower)
                    if kind not in minima or v< A(minima[kind]):minima[kind]=lower
                continue
            idx=max(range(3),key=lambda i:hi[i]-lo[i]);mid=(lo[idx]+hi[idx])/2
            if not lo[idx]<mid<hi[idx] or hi[idx]-lo[idx]<2**-40:
                todo.append((lo,hi));failure='Unresolved box at minimum dyadic width';break
            lh=list(hi);rl=list(lo);lh[idx]=mid;rl[idx]=mid
            todo.extend([(tuple(rl),hi),(lo,tuple(lh))]);counts['split']=counts.get('split',0)+1
            if count%20000==0:print(cellname,vertex,count,len(todo),round(time.monotonic()-start,2),flush=True)
        if not todo:status='complete'
    except KeyboardInterrupt:
        failure='Interrupted; remaining boxes retained'
    out=dict(status=status,cell=cellname,vertex=vertex,precision_bits=ctx.prec,nodes=count,pending=len(todo),
        counts=counts,seconds=time.monotonic()-start,scaled_target=str(target),local_checks=locals_,support=support,
        tangent_solve=solve,z_bracket=c['z_bracket'],accepted_partition_sha256=digest.hexdigest(),
        accepted_lower_bounds=minima,remaining_boxes=todo,failure=failure,
        inputs_sha256=hashlib.sha256(ec.SOURCE.read_bytes()).hexdigest(),
        common_sha256=hashlib.sha256(Path(ec.__file__).read_bytes()).hexdigest(),
        template_builder_sha256=hashlib.sha256((HERE/'build_templates.py').read_bytes()).hexdigest(),
        program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        template_sha256=hashlib.sha256((HERE/'generated_templates.py').read_bytes()).hexdigest())
    path=ec.OUTPUT/f'verified_{cellname}_{vertex}.json';path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['remaining_boxes','tangent_solve','local_checks']},indent=2),flush=True)
    return out

if __name__=='__main__':
    assert len(sys.argv)>=3,'Usage: verify_endpoint.py CELL VERTEX_OR_apex [budget]'
    out=verify_job(sys.argv[1],sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 2000000)
    if out['status']!='complete':raise SystemExit(1)
