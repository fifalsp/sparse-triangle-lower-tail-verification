"""Untrusted rational interval proof emitter shared by cover-region generators.
The emitted Lean source, not this Python program, establishes the enclosures.
"""
from fractions import Fraction as F
lines=[]
def emit(s=''):lines.append(s)
def q(x):
 x=F(x)
 return f'({x.numerator}/{x.denominator} : ℝ)' if x.denominator!=1 else f'({x.numerator} : ℝ)'
def outward(l,u):
 scale=10**10
 return F(l.numerator*scale//l.denominator,scale),F(-((-u.numerator*scale)//u.denominator),scale)
class Node:
 count=0
 def __init__(self,e,l,u,h):self.e,self.l,self.u,self.h=e,F(l),F(u),h
 @staticmethod
 def c(x):return Node(q(x),x,x,f'(Bounds.refl {q(x)})')
 def op(self,b,op):
  if op=='+':l,u=self.l+b.l,self.u+b.u;pr=f'{self.h}.add {b.h}'
  elif op=='-':l,u=self.l-b.u,self.u-b.l;pr=f'{self.h}.sub {b.h}'
  elif op=='*':
   corners=[self.l*b.l,self.l*b.u,self.u*b.l,self.u*b.u];l,u=min(corners),max(corners)
   l,u=outward(l,u)
   pr=f'{self.h}.mul_corners {b.h} '+' '.join(['(by norm_num)']*8)
  elif op=='/':
   assert self.l>=0 and b.l>0
   l,u=self.l/b.u,self.u/b.l;pr=f'{self.h}.div_pos {b.h} (by norm_num) (by norm_num)'
  l,u=outward(l,u)
  Node.count+=1;n=f'v{Node.count}';h=f'h{Node.count}'
  emit(f'  let {n} : ℝ := {self.e}{op}{b.e}')
  emit(f'  have {h} : Bounds {n} {q(l)} {q(u)} := by')
  if op=='*':emit(f'    exact {pr}')
  else:emit(f'    exact ({pr}).weaken (by norm_num) (by norm_num)')
  return Node(n,l,u,h)
 def __add__(s,b):return s.op(b,'+')
 def __sub__(s,b):return s.op(b,'-')
 def __mul__(s,b):return s.op(b,'*')
 def __truediv__(s,b):return s.op(b,'/')
 def neg(s):return Node.c(0)-s
 def pow(s,n):
  if n==0:return Node.c(1)
  r=s
  for _ in range(n-1):r=r*s
  return r
 def pin(s,e,name,unfolds=''):
  emit(f'  have {name} : Bounds ({e}) {q(s.l)} {q(s.u)} := by')
  emit(f'    convert {s.h} using 1 <;>')
  emit('      simp only ['+','.join(['certificateFeature','cyclicAverage','coverEdgeResidual','coverVertexResidual','edgeTest','vertexTest','coverCycle','logBoxEdges','coverS1Vertex0','relaxationMultiplier','relaxationVertexMean','entropy','vertexEntropy','criticalObservable','certificateHoeffding','Matrix.cons_val','Matrix.cons_val_zero','Matrix.cons_val_succ',"Matrix.cons_val_zero'","Matrix.cons_val_succ'"]+[f'v{i}' for i in range(1,Node.count+1)])+'] <;> ring')
  return Node(f'({e})',s.l,s.u,name)
 def nonneg(s,h):
  if s.l>=0:return s
  emit(f'  have {s.h}p : Bounds {s.e} 0 {q(s.u)} := ⟨{h},{s.h}.2⟩')
  return Node(s.e,0,s.u,s.h+'p')


def reset():
 lines.clear()
 Node.count=0

def modularize(source, prefix, pin_names, final_header):
 """Factor a proof DAG into individually checked intermediate theorems."""
 import re
 body=source
 pat=re.compile(r'^  (?:have|let) (\w+)\b',re.M)
 starts=list(pat.finditer(body));blocks={}
 for i,mt in enumerate(starts):
  blocks[mt.group(1)]=body[mt.start():starts[i+1].start() if i+1<len(starts) else len(body)].rstrip()
 order=list(blocks);known=set();out=[]
 def needed(name,root):
  if name in known and name!=root:return {name}
  text='\n'.join(l for l in blocks[name].splitlines() if not re.match(r'\s*(?:(?:simp|dsimp) only|norm_num \[)',l))
  ds={n for n in re.findall(r'\b\w+\b',text) if n in blocks and n!=name}
  res={name}
  for dep in ds:res |= needed(dep,root)
  return res
 def trim(block,uses):
  for name in order:
   if name.startswith('v') and name not in uses:
    block=re.sub(r'(?<=[\[,])'+name+r'(?=[,\]])','',block)
  return re.sub(r',+',',',block).replace('[,','[').replace(',]',']')
 def emit_deps(uses):
  for dep in order:
   if dep not in uses:continue
   if dep in known:out.append(f'  have {dep} := {prefix}_{dep}_bounds hq')
   else:out.append(trim(blocks[dep],uses))
 for name in pin_names:
  uses=needed(name,name)
  goal=blocks[name].splitlines()[0].split(' : ',1)[1].rsplit(' := by',1)[0]
  out.append(f'theorem {prefix}_{name}_bounds {{qv : EdgeTriple}} (hq : qv ∈ {prefix}Box.region) :\n    {goal} := by')
  emit_deps(uses);out.append(f'  exact {name}\n');known.add(name)
 out.append(final_header);emit_deps(needed('heq','heq'))
 return '\n'.join(out)
