#!/usr/bin/env python3
"""Propose coexistence-digit certificates. All acceptance is by the Lean kernel."""
from pathlib import Path
from decimal import Decimal, getcontext, ROUND_FLOOR
from fractions import Fraction as F
import cover_interval_codegen as cg
getcontext().prec=85
q,emit,Node=cg.q,cg.emit,cg.Node

def dec(x): return Decimal(x.numerator)/Decimal(x.denominator)
def bracket(x,p=32):
    n=int((x*10**p).to_integral_value(rounding=ROUND_FLOOR))
    return F(n-1,10**p),F(n+2,10**p)
def outward(l,u):
    scale=10**36
    return F(l.numerator*scale//l.denominator,scale),F(-((-u.numerator*scale)//u.denominator),scale)
cg.outward=outward

def root(g):
    s=Decimal('.265')
    for _ in range(60): s-=(s.ln()+3*g*s*s)/(1/s+6*g*s)
    return s

def value(z):
    L=-z.ln();b=(-2*z*L/(1-z)**2).exp();mu=2*L/((1-z)**2*b*b)
    s=root(mu/3);a=z*b;t=(a**3+3*a*b*b)/4
    return s-(a+b)/2-2*mu/3*(t-s**3)

def logcert(name,x,k,n):
    lo,hi=bracket(-dec(x).ln())
    emit(f'theorem {name} : Bounds (-Real.log {q(x)}) {q(lo)} {q(hi)} := by')
    emit(f'  have h := Real.abs_log_sub_add_sum_range_le (x := {q(1-2**k*x)}) (by norm_num) {n}')
    emit('  norm_num [Finset.sum_range_succ] at h\n  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2')
    emit(f'  have he : Real.log {q(2**k*x)}={k}*Real.log 2+Real.log {q(x)} := by')
    emit(f'    rw [show {q(2**k*x)}=(2:ℝ)^{k}*{q(x)} by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]\n    norm_num')
    emit('  rw [he] at hl hu\n  have h2l := log_two_bounds_40.1\n  have h2u := log_two_bounds_40.2\n  constructor <;> linarith\n')
    return lo,hi

def expcert(name,x):
    lo,hi=bracket(dec(x).exp())
    emit(f'theorem {name} : Bounds (Real.exp {q(x)}) {q(lo)} {q(hi)} := by')
    emit(f'  have h := Real.exp_bound (x := {q(x)}) (by norm_num) (n := 20) (by norm_num)')
    emit('  norm_num [Finset.sum_range_succ,Nat.factorial] at h\n  have hl := (abs_le.mp h).1\n  have hu := (abs_le.mp h).2\n  constructor <;> linarith\n')
    return lo,hi

def unfolds():return ','.join(f'v{i}'for i in range(1,Node.count+1))
def bounds_type(e,node):return f'Bounds ({e}) {q(node.l)} {q(node.u)}'
def identity(actual,node,extra=''):
    emit(f'  have he : {actual}={node.e} := by')
    if extra:emit('    '+extra)
    emit(f'    dsimp only [{unfolds()},branchMu,branchA,branchRho,balancedTriangle]\n    ring')
    emit(f'  rw [he]\n  exact {node.h}\n')

def branch_data(tag,zlo,zhi):
    assert 0<zlo<=zhi<1
    lr=logcert(tag+'_log_lower',zlo,14,90)
    ur=lr if zlo==zhi else logcert(tag+'_log_upper',zhi,14,90)
    Ll,Lu=ur[0],lr[1];hz=f'z ∈ Icc {q(zlo)} {q(zhi)}'
    emit(f'theorem {tag}_log {{z : ℝ}} (hz : {hz}) : Bounds (branchLog z) {q(Ll)} {q(Lu)} := by')
    emit(f'  have hz0 : 0<z := lt_of_lt_of_le (by norm_num : 0<{q(zlo)}) hz.1')
    emit(f'  have hlo := Real.log_le_log (by norm_num : 0<{q(zlo)}) hz.1\n  have hhi := Real.log_le_log hz0 hz.2')
    upper_name=tag+'_log_lower' if zlo==zhi else tag+'_log_upper'
    emit(f'  have hl := {upper_name}.1\n  have hu := {tag}_log_lower.2\n  rw [branchLog_eq_neg_log]\n  constructor <;> linarith\n')
    Node.count=0;start=len(cg.lines)
    Z=Node('z',zlo,zhi,'hZ');L=Node('(branchLog z)',Ll,Lu,'hL');one=Node.c(1);two=Node.c(2)
    E=two*Z*L/(one-Z).pow(2);calc=cg.lines[start:];del cg.lines[start:]
    emit(f'theorem {tag}_exponent {{z : ℝ}} (hz : {hz}) : {bounds_type("2*z*branchLog z/(1-z)^2",E)} := by')
    emit(f'  have hZ : Bounds z {q(zlo)} {q(zhi)} := hz\n  have hL := {tag}_log hz');cg.lines.extend(calc)
    identity('2*z*branchLog z/(1-z)^2',E)
    Bl=expcert(tag+'_exp_lower',-E.u)[0];Bu=expcert(tag+'_exp_upper',-E.l)[1]
    emit(f'theorem {tag}_B {{z : ℝ}} (hz : {hz}) : Bounds (branchB z) {q(Bl)} {q(Bu)} := by')
    emit(f'  have hE := {tag}_exponent hz\n  have hlo := Real.exp_le_exp.mpr (neg_le_neg hE.2)\n  have hhi := Real.exp_le_exp.mpr (neg_le_neg hE.1)')
    emit('  have he : branchB z=Real.exp (-(2*z*branchLog z/(1-z)^2)) := by unfold branchB;congr 1;ring')
    emit(f'  rw [← he] at hlo hhi\n  have hl := {tag}_exp_lower.1\n  have hu := {tag}_exp_upper.2\n  constructor <;> linarith\n')
    kl=bracket(((dec(zlo)**3+3*dec(zlo))/4).ln().__truediv__(3).exp())[0]
    ku=bracket(((dec(zhi)**3+3*dec(zhi))/4).ln().__truediv__(3).exp())[1]
    emit(f'theorem {tag}_K {{z : ℝ}} (hz : {hz}) : Bounds (kappa z) {q(kl)} {q(ku)} := by')
    emit(f'  have hlo := kappa_mono_nonneg (by norm_num : 0≤{q(zlo)}) hz.1\n  have hhi := kappa_mono_nonneg (le_trans (by norm_num : 0≤{q(zlo)}) hz.1) hz.2')
    for side,k,x in [('l',kl,zlo),('u',ku,zhi)]:
        typ=f'{q(k)}≤kappa {q(x)}' if side=='l' else f'kappa {q(x)}≤{q(k)}'
        emit(f'  have h{side} : {typ} := by\n    apply (show Odd (3:ℕ) by decide).strictMono_pow.le_iff_le.mp\n    rw [kappa_cube (by norm_num : 0≤{q(x)})]\n    norm_num')
    emit('  exact ⟨hl.trans hlo,hhi.trans hu⟩\n')
    Node.count=0;start=len(cg.lines)
    Z=Node('z',zlo,zhi,'hZ');L=Node('(branchLog z)',Ll,Lu,'hL');B=Node('(branchB z)',Bl,Bu,'hB');K=Node('(kappa z)',kl,ku,'hK')
    A=Z*B;Mu=two*L/((one-Z).pow(2)*B.pow(2));R=K*B;M=(A+B)/two;T=(A.pow(3)+Node.c(3)*A*B.pow(2))/Node.c(4);P=one-M-two*Mu*T/Node.c(3)
    calc=cg.lines[start:];del cg.lines[start:]
    actual=['branchMu z','branchRho z','(branchA z+branchB z)/2','balancedTriangle (branchA z) (branchB z)','balancedPenalty (branchMu z/3) (branchA z) (branchB z)'];nodes=[Mu,R,M,T,P]
    emit(f'theorem {tag}_data {{z : ℝ}} (hz : {hz}) :\n    '+' ∧\n    '.join(bounds_type(e,n)for e,n in zip(actual,nodes))+' := by')
    emit(f'  have hZ : Bounds z {q(zlo)} {q(zhi)} := hz\n  have hL := {tag}_log hz\n  have hB := {tag}_B hz\n  have hK := {tag}_K hz');cg.lines.extend(calc)
    emit('  refine ⟨?_,?_,?_,?_,?_⟩')
    for e,n in zip(actual,nodes):
        emit(f'  · have he : {e}={n.e} := by')
        if n is P:
            emit(f'      rw [branchPenalty_stationary ⟨lt_of_lt_of_le (by norm_num : 0<{q(zlo)}) hz.1,lt_of_le_of_lt hz.2 (by norm_num : {q(zhi)}<1)⟩]')
        emit(f'      dsimp only [{unfolds()},branchMu,branchA,branchRho,balancedTriangle]')
        if n is not R and n is not M: emit('      ring')
        emit(f'    rw [he]\n    exact {n.h}')
    emit('')
    return dict(tag=tag,zlo=zlo,zhi=zhi,mu=Mu,rho=R,mean=M,triangle=T,phi=P)

def root_data(d):
    tag=d['tag'];Mu=d['mu'];sl=bracket(root(dec(Mu.u)/3),26)[0];su=bracket(root(dec(Mu.l)/3),26)[1]
    logs={}
    for side,s in [('lower',sl),('upper',su)]:
        logs[side]=logcert(tag+'_root_log_'+side,s,2,35)
        Node.count=0;start=len(cg.lines);M=Node('(branchMu z)',Mu.l,Mu.u,'hM');S=Node.c(s);LS=Node('(-Real.log '+q(s)+')',*logs[side],tag+'_root_log_'+side);V=M*S.pow(2)-LS;calc=cg.lines[start:];del cg.lines[start:]
        assert V.u<0 if side=='lower' else V.l>0,(tag,side,float(V.l),float(V.u))
        hz=f'z ∈ Icc {q(d["zlo"])} {q(d["zhi"])}';ineq=f'constantEquation (branchMu z/3) {q(s)}≤0' if side=='lower' else f'0≤constantEquation (branchMu z/3) {q(s)}'
        emit(f'theorem {tag}_root_sign_{side} {{z : ℝ}} (hz : {hz}) : {ineq} := by\n  have hM := ({tag}_data hz).1');cg.lines.extend(calc)
        emit(f'  have he : constantEquation (branchMu z/3) {q(s)}={V.e} := by\n    dsimp only [{unfolds()}]\n    unfold constantEquation\n    ring\n  rw [he]')
        emit(f'  exact {V.h}.2.trans (by norm_num)' if side=='lower' else f'  exact le_trans (by norm_num) {V.h}.1');emit('')
    emit(f'theorem {tag}_root {{z : ℝ}} (hz : {hz}) : Bounds (constantRoot (branchMu z/3)) {q(sl)} {q(su)} := by')
    emit(f'  have hγ : 0<branchMu z/3 := div_pos (branchMu_pos (lt_of_lt_of_le (by norm_num : 0<{q(d["zlo"])}) hz.1) (lt_of_le_of_lt hz.2 (by norm_num : {q(d["zhi"])}<1))) (by norm_num)')
    emit(f'  exact constantRoot_bounds_of_signs hγ (by norm_num) ({tag}_root_sign_lower hz) ({tag}_root_sign_upper hz) (by norm_num)\n')
    d['root']=(sl,su)

def endpoint_gap(d):
    tag,z=d['tag'],d['zlo'];assert z==d['zhi'];Node.count=0;start=len(cg.lines)
    M=Node('(branchMu '+q(z)+')',d['mu'].l,d['mu'].u,'hM');A=Node('((branchA '+q(z)+'+branchB '+q(z)+')/2)',d['mean'].l,d['mean'].u,'hA');T=Node('(balancedTriangle (branchA '+q(z)+') (branchB '+q(z)+'))',d['triangle'].l,d['triangle'].u,'hT');S=Node('(constantRoot (branchMu '+q(z)+'/3))',*d['root'],'hS')
    V=S-A-Node.c(2)*M/Node.c(3)*(T-S.pow(3));calc=cg.lines[start:];del cg.lines[start:];neg=tag=='lower';assert V.u<0 if neg else V.l>0,(float(V.l),float(V.u))
    goal=f'penalizedGap {q(z)}<0' if neg else f'0<penalizedGap {q(z)}'
    emit(f'theorem {tag}_gap : {goal} := by\n  have hd := {tag}_data (z := {q(z)}) ⟨le_rfl,le_rfl⟩\n  have hM := hd.1\n  have hA := hd.2.2.1\n  have hT := hd.2.2.2.1\n  have hS := {tag}_root (z := {q(z)}) ⟨le_rfl,le_rfl⟩');cg.lines.extend(calc)
    emit(f'  have he : penalizedGap {q(z)}={V.e} := by\n    rw [penalizedGap_stationary (by norm_num : {q(z)} ∈ Ioo (0:ℝ) 1)]\n    dsimp only [{unfolds()}]\n    ring\n  rw [he]')
    emit(f'  exact lt_of_le_of_lt {V.h}.2 (by norm_num)' if neg else f'  exact lt_of_lt_of_le (by norm_num) {V.h}.1');emit('')
    print('Proposed',tag,'gap bounds:',float(V.l),float(V.u))

lo,hi=Decimal('8.352460192e-5'),Decimal('8.352460193e-5')
for _ in range(120):
    mid=(lo+hi)/2
    if value(mid)<0:lo=mid
    else:hi=mid
n=int(mid*10**24);zlo,zhi=F(n-1,10**24),F(n+2,10**24)
header='''import SparseLowerTail.Section07.PenalizedDigitsCore

/-! Generated coexistence certificates; all proposed enclosures are checked in Lean. -/
noncomputable section
open Set
namespace SparseLowerTail.Section07.PenalizedDigits
open Section04 Numerics
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
'''
for tag,l,u in [('lower',zlo,zlo),('upper',zhi,zhi),('crossing',zlo,zhi)]:
    d=branch_data(tag,l,u);root_data(d)
    if tag!='crossing':endpoint_gap(d)
    else:common=d
emit(f'def zLower : ℝ := {q(zlo)}\ndef zUpper : ℝ := {q(zhi)}\n')
emit('theorem crossing_bracket : zLower<penalizedCrossing ∧ penalizedCrossing<zUpper := by\n  constructor\n  · rcases lt_trichotomy zLower penalizedCrossing with h|h|h\n    · exact h\n    · have hh := lower_gap\n      change penalizedGap zLower<0 at hh\n      rw [h,penalizedCrossing_spec.2] at hh\n      linarith\n    · have hh := penalizedGap_pos_after_open ⟨h,lt_trans (by norm_num [zLower] : zLower<1/1000) foldPoint_bounds.1⟩\n      have hn := lower_gap\n      change penalizedGap zLower<0 at hn\n      linarith\n  · rcases lt_trichotomy penalizedCrossing zUpper with h|h|h\n    · exact h\n    · have hh := upper_gap\n      change 0<penalizedGap zUpper at hh\n      rw [← h,penalizedCrossing_spec.2] at hh\n      linarith\n    · have hh := penalizedGap_neg_before ⟨by norm_num [zUpper],h⟩\n      have hp := upper_gap\n      change 0<penalizedGap zUpper at hp\n      linarith\n')
emit('theorem printed_crossing_bracket : (8352460192/10^14:ℝ)<penalizedCrossing ∧ penalizedCrossing<(8352460193/10^14:ℝ) := by\n  have h := crossing_bracket\n  norm_num [zLower,zUpper] at h\n  constructor <;> linarith\n')
mu,rho,phi=common['mu'],common['rho'],common['phi'];sl,su=common['root']
targets=[(F('6.280969860'),F('6.280969861')),(F('0.4999589178'),F('0.4999589179')),(F('0.03965310391'),F('0.03965310392')),(F('0.2653474271'),F('0.2653474272'))]
for (l,u),(a,b)in zip([(mu.l/3,mu.u/3),(phi.l,phi.u),(rho.l,rho.u),(sl,su)],targets):assert a<=l<=u<=b,(float(l),float(u),a,b)
emit('theorem coexistence_digits :\n    Bounds criticalPenalty (6280969860/10^9) (6280969861/10^9) ∧\n    Bounds (penalizedValue criticalPenalty) (4999589178/10^10) (4999589179/10^10) ∧\n    Bounds smallTarget (3965310391/10^11) (3965310392/10^11) ∧\n    Bounds largeTarget (2653474271/10^10) (2653474272/10^10) := by')
emit('  have hz : penalizedCrossing ∈ Icc zLower zUpper := ⟨crossing_bracket.1.le,crossing_bracket.2.le⟩\n  have hd := crossing_data hz\n  have hs := crossing_root hz\n  refine ⟨?_,?_,?_,?_⟩\n  · unfold criticalPenalty Bounds\n    constructor <;> linarith [hd.1.1,hd.1.2]\n  · rw [penalizedValue_at_critical.2]\n    exact hd.2.2.2.2.weaken (by norm_num) (by norm_num)\n  · exact hd.2.1.weaken (by norm_num) (by norm_num)\n  · exact hs.weaken (by norm_num) (by norm_num)\n')
emit('theorem printed_endpoint_signs : penalizedGap (8352460192/10^14:ℝ)<0 ∧ 0<penalizedGap (8352460193/10^14:ℝ) := by\n  refine ⟨penalizedGap_neg_before ⟨by norm_num,printed_crossing_bracket.1⟩,?_⟩\n  exact penalizedGap_pos_after_open ⟨printed_crossing_bracket.2,lt_trans (by norm_num : (8352460193/10^14:ℝ)<1/1000) foldPoint_bounds.1⟩\n')
emit('theorem printed_constants :\n    ((8352460192/10^14:ℝ)<penalizedCrossing ∧ penalizedCrossing<(8352460193/10^14:ℝ)) ∧\n    Bounds criticalPenalty (6280969860/10^9) (6280969861/10^9) ∧\n    Bounds (penalizedValue criticalPenalty) (4999589178/10^10) (4999589179/10^10) ∧\n    Bounds smallTarget (3965310391/10^11) (3965310392/10^11) ∧\n    Bounds largeTarget (2653474271/10^10) (2653474272/10^10) :=\n  ⟨printed_crossing_bracket,coexistence_digits⟩\n')
emit('end SparseLowerTail.Section07.PenalizedDigits')
Path('SparseLowerTail/Section07/PenalizedDigits.lean').write_text(header+'\n'.join(cg.lines)+'\n')
print('Proposed coexistence bracket',zlo,zhi)
