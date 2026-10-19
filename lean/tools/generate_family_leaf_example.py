#!/usr/bin/env python3
"""Propose an end-to-end family leaf. Lean checks all arithmetic and formulas.
Python's interval arithmetic is a data generator, not part of the trusted proof.
"""
from fractions import Fraction as F
from pathlib import Path
from generate_exp_endpoints import endpoint,rat
S=2**60
class I:
 def __init__(self,l,u=None):
  if u is None:
   f=F(l);self.l=f.numerator*S//f.denominator;self.u=-((-f.numerator*S)//f.denominator)
  else:self.l,self.u=l,u
 @staticmethod
 def coerce(x):return x if isinstance(x,I) else I(x)
 def __add__(a,b):
  b=I.coerce(b);return I(a.l+b.l,a.u+b.u)
 __radd__=__add__
 def __neg__(a):return I(-a.u,-a.l)
 def __sub__(a,b):return a+-I.coerce(b)
 def __rsub__(a,b):return I.coerce(b)+-a
 def __mul__(a,b):
  b=I.coerce(b);v=[a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u];return I(min(v)//S,-((-max(v))//S))
 __rmul__=__mul__
 def inv(a):
  if a.l>0:return I(S*S//a.u,-((-S*S)//a.l))
  if a.u<0:return -(-a).inv()
  raise ValueError('zero in reciprocal')
 def __truediv__(a,b):return a*I.coerce(b).inv()
 def __pow__(a,n):
  r=I(1)
  for _ in range(n):r=r*a
  return r
 def lean(a):return f'⟨{a.l},{a.u}⟩'
def ep(q):return endpoint(q,20,60)
def expbox(a,b):return I(I(b[4]).l,I(a[5]).u)
def coeff(z,L,b):
 D=6*L**2*z**2+3*L*z**3-L*z**2-L*z-L-z**3+3*z**2-3*z+1
 d1=z*(z-1)*(z+1)*(L+z-1)*(2*L+z-1)/(2*D)
 d2=z*(z-1)**2*(2*L*z+z**2-1)/(2*D)
 d3=-z*(z-1)**3*(3*L*z+L+2*z**2-2)/(2*(z+1)*D)
 d4=(z-1)**4*(2*L*z+z**2-1)/(2*L*(z+1)*D)
 mu=2*L/(1-z)**2;t=(z**3+3*z)/4
 d0=-d1*((1+z)/2)+d2*mu*t-t/3
 return [b**3*d0,b**2*d1,b**2*d2,b**3*d3,b**2*d4,b*mu*d3,mu*d4]
def main():
 lo,hi=F('3.9'),F('3.901');ql,qh=F(0),F('0.01')
 elo,ehi=ep(lo),ep(hi);L=I(I(lo).l,I(hi).u);z=expbox(elo,ehi)
 delta=2*z*L/(1-z)**2;dlo,dhi=ep(F(delta.l,S)),ep(F(delta.u,S));b=expbox(dlo,dhi)
 cs=coeff(z,L,b);eql,eqh=ep(ql),ep(qh)
 print('coefficient ranges',[(v.l/S,v.u/S) for v in cs])
 lines=['import SparseLowerTail.Section08.FamilyBoxIntervals','',
  '/-! One complete family leaf: L in [3.9,3.901], each q in [0,0.01].',
  'The generator proposes data; every validity and positivity check is proved here. -/',
  'namespace SparseLowerTail.Certificate.FamilyLeafExample','open Numerics Section04',
  'set_option maxRecDepth 100000','set_option maxHeartbeats 4000000','']
 for name,e in [('logLower',elo),('logUpper',ehi),('deltaLower',dlo),('deltaUpper',dhi),('qLower',eql),('qUpper',eqh)]:
  q,n,l,u,Lb,Ub=e
  lines +=[f'def {name} : ExpEndpointCertificate := ⟨{rat(q)},{n},{rat(l)},{rat(u)},{rat(Lb)},{rat(Ub)}⟩',f'theorem {name}_valid : {name}.Valid := by decide +kernel','']
 lines +=['def parameter : FamilyParameterCertificate :=',f'  ⟨logLower,logUpper,deltaLower,deltaUpper,{delta.lean()}⟩',
 'theorem parameter_valid : parameter.Valid := by',
 '  refine ⟨logLower_valid,logUpper_valid,deltaLower_valid,deltaUpper_valid,?_,?_,?_⟩',
 '  all_goals decide +kernel','',
 'def certificate : FamilyBoxCertificate :=',
 '  ⟨parameter,!['+','.join(v.lean() for v in cs)+'],fun _ => qLower,fun _ => qUpper⟩',
 'theorem certificate_valid : certificate.Valid := by',
 '  refine ⟨parameter_valid,?_,fun _ => qLower_valid,fun _ => qUpper_valid⟩',
 '  intro i; fin_cases i <;> decide +kernel','',
 'theorem positive_lower : 0<(familyPhiExpr.dyadicEval certificate.variableIntervals).lower := by',
 '  decide +kernel','',
 'theorem phi_positive {z : ℝ} (hz : 0<z)',
 '    (hL : Bounds (branchLog z) (39/10) (3901/1000))',
 '    {q : FamilyVector} (hq : ∀i,Bounds (q i) 0 (1/100)) : 0<familyPhi z q := by',
 '  apply certificate.phi_positive certificate_valid positive_lower hz',
 '  · simpa [certificate,parameter,logLower,logUpper] using hL',
 '  · simpa [certificate,qLower,qUpper] using hq','',
 'end SparseLowerTail.Certificate.FamilyLeafExample','']
 out=Path(__file__).resolve().parents[1]/'SparseLowerTail/Section08/FamilyLeafExample.lean';out.write_text('\n'.join(lines))
if __name__=='__main__':main()
