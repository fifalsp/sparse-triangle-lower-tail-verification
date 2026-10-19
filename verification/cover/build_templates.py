"""Rebuild the source's exact scaled certificate and all q derivatives.

No floating constants enter the templates: we work with 3 Psi.
Default/--check rebuilds in memory and compares without writing.
Use --write explicitly to regenerate the committed templates and manifest.
"""
from pathlib import Path
import sys, argparse
if not __debug__: raise RuntimeError("Verification requires assertions; do not use Python -O or PYTHONOPTIMIZE.")
import sympy as s,inspect,json,hashlib
parser=argparse.ArgumentParser(description=__doc__)
group=parser.add_mutually_exclusive_group()
group.add_argument("--check", action="store_true", help="verify exact regeneration without changing files (default)")
group.add_argument("--write", action="store_true", help="regenerate templates and their source manifest")
options=parser.parse_args()
HERE=Path(__file__).resolve().parent
q=s.symbols('q0:3');x=s.symbols('x0:3');th=s.symbols('th0:12')
lam,mu,kbar,t,m,F,om=s.symbols('lam mu kbar t m F om')
h=[1-(1+qi)*xi for qi,xi in zip(q,x)]
k=[2*hi+qi*xi for qi,xi,hi in zip(q,x,h)]
g=[xi+om*hi for xi,hi in zip(x,h)]
phi=[(1,xi,xi**2,xi**3,-qi*xi) for qi,xi in zip(q,x)]
chi=[(xi,xi**3,xi**4,-qi*xi) for qi,xi in zip(q,x)]
E=[sum(x)-3*m,3*(s.prod(x)-t),sum(h)-3*F]
for j in range(5):E.append(sum(phi[i][j]*(-q[i]+mu*s.prod(x[k] for k in range(3) if k!=i)) for i in range(3)))
for j in range(4):E.append(sum(chi[i][j]*(sum(k[l] for l in range(3) if l!=i)-2*kbar) for i in range(3)))
H=sum(gi**2 for gi in g)-2*sum(g[i]*g[j] for i in range(3) for j in range(i+1,3))+3*(m+om*F)**2
Psi=-sum(ti*ei for ti,ei in zip(th,E))-lam*H
indices=[()]+[(i,) for i in range(3)]+[(i,j) for i in range(3) for j in range(i,3)]+[(i,j,k) for i in range(3) for j in range(i,3) for k in range(j,3)]
def diff(expr,i):return s.diff(expr,q[i])-x[i]*s.diff(expr,x[i])
exprs={():s.expand(Psi)}
for idx in indices[1:]:exprs[idx]=s.expand(diff(exprs[idx[:-1]],idx[-1]))
args=(*q,*x,*th,lam,mu,kbar,t,m,F,om)
parts=['"""Generated exact integer-coefficient templates for 3 Psi; see build_templates.py."""\n']
for name,inds in [('value',[()]),('all_derivatives',indices),('value_gradient',indices[:4]),('value_hessian',indices[:10])]:
 fn=s.lambdify(args,[exprs[i] for i in inds],modules=[],cse=True)
 code=inspect.getsource(fn).replace('_lambdifygenerated',name)
 assert not any(isinstance(a,s.Float) for e in [exprs[i] for i in inds] for a in s.preorder_traversal(e))
 parts.append(code)
generated='\n'.join(parts)
manifest=dict(indices=indices,generated_sha256=hashlib.sha256(generated.encode()).hexdigest(),
    source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    integer_coefficients=True,scaled_certificate='3 Psi')
if options.write:
    (HERE/'generated_templates.py').write_text(generated)
    (HERE/'template_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('Generated exact value/derivative templates',flush=True)
else:
    assert (HERE/'generated_templates.py').read_text()==generated, 'Generated templates do not match exact symbolic reconstruction'
    saved=json.loads((HERE/'template_manifest.json').read_text())
    assert saved['generated_sha256']==manifest['generated_sha256']
    assert saved['indices']==[list(i) for i in indices]
    assert saved['integer_coefficients'] is True and saved['scaled_certificate']=='3 Psi'
    assert saved['source_sha256']==manifest['source_sha256'], 'Template-builder source digest mismatch'
    print(json.dumps(dict(status='complete',mode='check',templates_sha256=manifest['generated_sha256'],derivative_count=len(indices),scaled_certificate='3 Psi')),flush=True)
