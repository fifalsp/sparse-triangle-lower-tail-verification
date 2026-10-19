# Shorter proofs found during formalization

Updated: 2026-10-19. This is a companion to the manuscript, not an edit to it.
Stable identifiers below survive changes to theorem numbering. The source
snapshot and statement fingerprints are recorded in
[the proof map](../lean/proof-map.json).

A replacement marked **Lean checked** has a compiled proof of the stated
mathematical step. It does not mean the main theorem is completely formalized.
Explicit external inputs are listed in
[ASSUMPTIONS.md](../lean/ASSUMPTIONS.md); unresolved issues are in
[PROOF-ISSUES.md](../lean/PROOF-ISSUES.md).

| Note | Manuscript anchor | Replacement | Status |
| --- | --- | --- | --- |
| PS-001 | `lem:cut`(a) | Two positive-set selections instead of layer cake | Lean checked; no extra external input |
| PS-002 | `lem:spectral`, lower bound in `eq:s7degree` | Positive-part test gives d ≥ m/2 before spectral decomposition | Lean checked; positivity is derived from the proved penalized variation |
| PS-003 | `thm:rigidity`, Steps 4–5 | Compare the two row equations directly using log monotonicity | Lean checked, including the full local-rigidity assembly |
| PS-004 | `lem:penalized`, quadratic-form assertion | Evaluate at two opposite perturbations instead of differentiating twice | Lean checked |
| PS-005 | `prop:structural`, Step 4 | A fixed Taylor bound replaces differentiation of the exponential ratio | Lean checked |
| PS-006 | `lem:rowreduction`, approximate Euler equations | A polynomial identity proves both surrogate codegrees nonnegative | Lean checked; no extra hypothesis |

## Compact outline of the final argument

The following **conditional outline is Lean checked** in
[`ContinuationAssembly.lean`](../lean/SparseLowerTail/Section08/ContinuationAssembly.lean).
It follows the paper and makes the remaining work explicit; it is not a new
unconditional proof. Three internal statements remain to be discharged:

1. **Critical classification** (`prop:critical`), reduced elsewhere to the
   cover and apex certificates.
2. **Small-target classification** (`thm:smalltail`): all minimizers are the
   balanced branch for 0 < r ≤ r₋.
3. **Intermediate certificate** (`prop:family`): nonnegativity of Ψ and its
   allowed-pattern zero set at the branch parameters for r₋ ≤ r ≤ r*.

Given these inputs, let G be the set of subcritical targets at which every
minimizer is the balanced branch. The proved local rigidity and compactness
argument make G open. Critical classification and the left-limit argument give
an interval immediately below r* contained in G. Let r₀ be the infimum of the
left endpoints of all such intervals. Every r between r₀ and r* belongs to G.
If r₀ ≥ r₋, the boundary comparison gives matching branch cost and at least
the branch edge density for every minimizer at r₀. The certificate expectation
and tie exclusion then put r₀ in G. Openness extends the interval left of r₀,
a contradiction. Hence r₀ < r₋, and small-target classification fills the
remaining interval. Above and at r*, the already checked threshold reduction
uses critical classification. The balanced scalar analysis supplies the value
formula, uniqueness of the balanced pair, and certified transition interval. ∎

Exact final declaration: `Section08.mainTheorem_of_remaining_inputs`.
Its classical parameters are sampling, dyadic L¹ approximation, cut compactness,
pullback approximation and triangle counting. These are distinct from the three
unfinished internal inputs above. In particular, the new assembly does **not**
mean that `thm:main` is finished.

## PS-001 — the weighted cut-norm bound

**Statement.** Let D be an integrable real kernel on the probability square,
and let f,g be measurable functions taking values in [0,1]. Then

$$
\left|\iint D(x,y)f(x)g(y)\,dx\,dy\right|\le \|D\|_\square,
\qquad
\|D\|_\square:=\sup_{S,T}\left|\int_{S\times T}D\right|,
$$

where S,T range over measurable sets. Thus the replacement also removes the
unnecessary boundedness assumption on D.

**Complete replacement proof.** Put
$h(x)=\int D(x,y)g(y)\,dy$ and $S=\{h\ge0\}$. Since
$0\le f\le1$, we have $fh\le\mathbf1_S h$ almost everywhere. Fubini
therefore gives

$$
\iint Dfg\le\int_S h
 =\int g(y)k(y)\,dy,
\qquad k(y):=\int_S D(x,y)\,dx.
$$

Let $T=\{k\ge0\}$. Similarly $gk\le\mathbf1_T k$, and hence

$$
\iint Dfg\le\int_T k
 =\int_{S\times T}D\le\|D\|_\square.
$$

Apply the same argument to −D, whose cut norm equals that of D, to obtain
the opposite bound. This proves the assertion. All products are integrable
because f,g are bounded. If h or k is initially defined only almost
everywhere, use a measurable representative in defining its positive set;
this does not change any integral. ∎

**Lean correspondence.**
[`Section02/WeightedCut.lean`](../lean/SparseLowerTail/Section02/WeightedCut.lean):

- `exists_indicator_integral_ge`: the one-variable positive-set selection,
  including measurable representatives.
- `abs_weighted_integral_le_cutNorm`: the full absolute-value estimate for an
  arbitrary integrable kernel and almost-everywhere [0,1]-valued tests.

The downstream uniform functional estimate is proved in
[`Section06/RowStability.lean`](../lean/SparseLowerTail/Section06/RowStability.lean),
`rowFunctional_cut_bound`:

$$
|J_{U,\nu}(v)-J_{W,\mu}(v)|
\le \nu\|U-W\|_\square+|\nu-\mu|\qquad(\nu\ge0).
$$

Indeed, subtract the quadratic parts, use PS-001, and use
$0\le\langle v,T_Wv\rangle\le1$. This is exactly the estimate needed in
`thm:rigidity`, Step 1; it does not itself prove rigidity.

**Editorial use.** Replace only the proof of `lem:cut`(a). The other parts of
that lemma and their dependencies remain unchanged. If desired, strengthen
its hypothesis from bounded to integrable D.

## PS-002 — a direct lower degree bound

**Statement.** Let U≥0 be a bounded symmetric kernel on a probability space.
Set
$$
d(x)=\int U(x,y)\,dy,\qquad m=\int d,
\qquad K(x,y)=d(x)+d(y)-m-U(x,y).
$$
Suppose K has a nonnegative quadratic form. Then $d\ge m/2$ almost
everywhere. It suffices to assume positivity on bounded measurable test
functions; no spectral theorem or diagonal value of K is needed.

**Complete replacement proof.** Take $f=(m/2-d)_+$. Pointwise,
$df=(m/2)f-f^2$. Writing $A=\int f$ and $B=\int f^2$, expand the
quadratic form:

$$
\begin{aligned}
0\le\langle f,T_Kf\rangle
 &=2A\int df-mA^2-\langle f,T_Uf\rangle\\
 &=-2AB-\langle f,T_Uf\rangle\le-2AB\le0.
\end{aligned}
$$

Here U≥0 and f≥0 imply $\langle f,T_Uf\rangle\ge0$, while A,B≥0.
Thus AB=0. If A=0, nonnegativity gives f=0 almost everywhere; if B=0,
the same follows from $\int f^2=0$. Hence $(m/2-d)_+=0$, as required. ∎

**Lean correspondence.**
[`Section07/DegreeBounds.lean`](../lean/SparseLowerTail/Section07/DegreeBounds.lean),
`penalized_degree_lower`, applies this argument to the paper's actual
minimizers. The positivity used there is proved in
[`Section07/CenteredKernel.lean`](../lean/SparseLowerTail/Section07/CenteredKernel.lean),
`penalized_centeredKernel_positive`, from the penalized second variation.
The realization of vertex variations uses the already recorded classical
sampling input. The lower-degree proof adds no spectral assumption.

**Editorial use and limit.** This can move the lower degree bound before the
spectral part of `lem:spectral` and make that dependency simpler. It does
**not** replace the proof of the diagonal estimate, trace-class property, or
spectral tail inequalities: those conclusions still need their own arguments.
It is a structural simplification, not a claim that the whole lemma becomes
shorter if its original diagonal proof is retained verbatim.

## PS-003 — direct comparison of two stationary rows

This replaces the integration of the second variation along a segment of rows.
It proves the local row-uniqueness step, not the whole rigidity theorem.

Fix 0<a<b≤1 and μ>0 satisfying the balanced Euler equations. Let P be a
measurable set with mass p close to 1/2, let B be the two-block kernel with
within-block value a and cross-block value b, and put
$g=a\mathbf1_P+b\mathbf1_{P^c}$.
Write $Q_U(h)=\langle h,T_Uh\rangle$.

**Coercivity margin.** The positive balanced Hessian allows us, by continuity,
to choose η>0 such that
$$
A=\frac1{a+\eta}-\eta>0,\qquad
C=\frac1{b+\eta}-\eta>0,
\qquad
\left(\frac A{1/2+\eta}+\mu a\right)
\left(\frac C{1/2+\eta}+\mu a\right)>(\mu b)^2.
$$
At η=0 this is the determinant condition for twice the balanced Hessian.
Suppose both p and 1−p are at most 1/2+η and are positive. For any h in L²,
put $x=\int_P h$ and $y=\int_{P^c}h$. Blockwise Cauchy–Schwarz gives
$$
\begin{aligned}
\int\frac{h^2}{g+\eta}+\mu Q_B(h)-\eta\|h\|_2^2
&=A\int_P h^2+C\int_{P^c}h^2
  +\mu\{a(x^2+y^2)+2bxy\}\\
&\ge\left(\frac A p+\mu a\right)x^2
 +2\mu bxy+\left(\frac C{1-p}+\mu a\right)y^2\ge0.
\end{aligned}
$$
The final quadratic form is positive definite by the displayed determinant
condition. Hence
$$
\eta\|h\|_2^2\le\int\frac{h^2}{g+\eta}+\mu Q_B(h).
$$

**Compare the equations.** Suppose v,w take values in [0,1], have a common
positive lower bound, satisfy v,w≤g+η, and solve
$$
\log v+\nu T_Uv=0,\qquad \log w+\nu T_Uw=0
$$
almost everywhere. Set h=v−w. For positive s,t≤M,
$$
(s-t)(\log s-\log t)\ge\frac{(s-t)^2}{M},
$$
as follows by integrating the derivative 1/u between s and t. Applying this
pointwise with M=g+η, then subtracting and integrating the row equations, gives
$$
\int\frac{h^2}{g+\eta}
 \le\int h(\log v-\log w)=-\nu Q_U(h).
$$
All terms are integrable because the profiles are bounded above and away
from zero. If ν≥0 and $\|U-B\|_\infty\le\zeta$, then
$$
|Q_U(h)-Q_B(h)|\le\zeta\|h\|_1^2\le\zeta\|h\|_2^2,
\qquad |Q_B(h)|\le\|h\|_2^2.
$$
Combining the estimates yields
$$
\eta\|h\|_2^2\le\mu Q_B(h)-\nu Q_U(h)
 \le(\nu\zeta+|\nu-\mu|)\|h\|_2^2.
$$
Thus v=w almost everywhere whenever
$\nu\zeta+|\nu-\mu|<\eta$. ∎

**One radius suffices.** Take
$$
\delta=\min\left\{\eta,\frac a2,1,\frac{\eta}{2(\mu+2)}\right\}>0.
$$
Retain the assumptions that U is a graphon, ν≥0, and v,w are measurable
[0,1]-valued solutions of the displayed row equations. The conditions
$|p-1/2|<\delta$, $|\nu-\mu|<\delta$,
$\|U-B\|_\infty\le\delta$, and
$\|v-g\|_\infty,\|w-g\|_\infty\le\delta$ imply all required hypotheses:
δ≤a/2<1/2 ensures positive masses and v,w≥a/2; δ≤η gives the upper bounds;
ν<μ+1 and the last restriction make the error less than η. The other well
is handled by replacing P with its complement.

**Lean correspondence.**
[`Section06/RowRigidity.lean`](../lean/SparseLowerTail/Section06/RowRigidity.lean):
`log_strong_monotone`, `block_coercivity`,
`stationary_rows_eq_of_margin`, and `exists_stationary_row_radius`.
These proofs add no external hypotheses. The Lean coercivity lemma is stated
for bounded profiles, which covers the actual row differences; the displayed
Cauchy–Schwarz calculation also applies to arbitrary L² functions. Lean uses
the common denominator 1/2+η directly, so its intermediate coercivity step
does not need positive block masses. The final passage from equality of
rows within each class to a two-block graphon is proved in `RowsBipodal.lean`.
The complete sequential theorem, including the bijective relabeling step,
now compiles in `LocalRigidity.lean`, `eventually_bipodal_of_cutDistance`.

## PS-004 — the penalized quadratic inequality without a second derivative

Assume U is a graphon minimizing the triangle-constrained problem at
0<r<1 and also globally minimizes $F(W)+\gamma t(W)$, with γ≥0.
Use the already proved multiplier identity
$\mu_U=3\gamma$ and Euler equation
$\log U=-3\gamma C_U$. This note replaces the second-variation step only.

Take a bounded measurable mean-zero test ψ, scaled so that |ψ|≤1.
Reweight the vertex probability measure by 1+εψ and realize the resulting
kernel as a graphon $U^\varepsilon$, for |ε|≤1/2. The entropy and triangle
integrals give the exact cubic polynomial
$$
P(\varepsilon):=F(U^\varepsilon)+\gamma t(U^\varepsilon)
 =P(0)+A\varepsilon+B\varepsilon^2+C\varepsilon^3,
$$
whose quadratic coefficient, by cyclic symmetry of the triangle integral, is
$$
B=\iint\{h(U(x,y))+3\gamma U(x,y)C_U(x,y)\}\psi(x)\psi(y)\,dx\,dy.
$$
Global optimality gives $P(1/2),P(-1/2)\ge P(0)$. Adding cancels both
odd terms, so
$$
0\le P(1/2)+P(-1/2)-2P(0)=\frac12B.
$$
Since $h(u)=u\log u-u+1$, the Euler equation makes the expression in
braces equal to 1−U. Therefore
$$
0\le B=(\textstyle\int\psi)^2-\langle\psi,T_U\psi\rangle
 =-\langle\psi,T_U\psi\rangle.
$$
Scaling proves the assertion for all bounded mean-zero tests. For an
arbitrary mean-zero f in L², put
$f_n=\max\{-n,\min\{n,f\}\}-\int\max\{-n,\min\{n,f\}\}$.
Then f_n is bounded and mean zero, and f_n→f in L² by dominated convergence.
Because 0≤U≤1,
$$
|Q_U(f_n)-Q_U(f)|
 \le\|f_n-f\|_1(\|f_n\|_1+\|f\|_1)\longrightarrow0.
$$
Thus $Q_U(f)\le0$. ∎

**Lean correspondence.**
[`Section07/PenalizedSecondVariation.lean`](../lean/SparseLowerTail/Section07/PenalizedSecondVariation.lean):
`pair_weight_symmetric_sum`, `triple_weight_symmetric_sum`,
`penalized_vertex_quadratic_nonneg`, `penalized_quadratic_nonpos_unit`.
[`Section07/PenalizedQuadratic.lean`](../lean/SparseLowerTail/Section07/PenalizedQuadratic.lean)
proves the bounded-test extension, the centered truncation argument, and the
full L² conclusion. The actual reweighted graphons use only the recorded
classical sampling input. No differentiability of this polynomial is needed.

## PS-005 — a direct exponential coercivity estimate

For every μ ≥ 18,
$$
e^{0.27\mu}>\mu+\mu^2/4.
$$
**Complete replacement proof.** The first nine Taylor terms, all nonnegative,
give $e^{4.86}>120$ by exact rational arithmetic. Put $t=\mu-18\ge0$.
The standard inequality $e^x\ge1+x+x^2/2$ for $x\ge0$ yields
$$
e^{0.27\mu}
=e^{4.86}e^{0.27t}
>120(1+0.27t+0.27^2t^2/2).
$$
Subtracting $\mu+\mu^2/4=99+10t+t^2/4$ leaves
$21+22.4t+4.124t^2>0$. ∎

For the exact use in Step 4 of `prop:structural` (within the proof of
`thm:smalltail`), put $a=e^{-0.27\mu}$ and let $p\in[0,1]$.
The estimate gives $\mu a<1$. For
$$
A=a^{-1}-\mu ap,\qquad B=\mu\sqrt{p(1-p)},
\qquad C=1-\mu a(1-p),
$$
we have $C\ge1-\mu a>0$ and
$$
AC-B^2
=a^{-1}-\mu-\mu^2p(1-p)
 +\mu p(1-a)+\mu^2p(1-p)a^2
\ge a^{-1}-\mu-\mu^2/4>0.
$$
Thus $AX^2-2BXY+CY^2\le0$ forces $X=Y=0$, using
$$
C(AX^2-2BXY+CY^2)=(CY-BX)^2+(AC-B^2)X^2.
$$

**Lean correspondence.**
[`SmallRigidityCoercivity.lean`](../lean/SparseLowerTail/Section07/SmallRigidityCoercivity.lean):
`exp_486_gt_120`, `small_rigidity_exp_margin`,
`block_rigidity_determinant`, and `small_rigidity_block_norms_zero`.
These are unconditional scalar results. The required blockwise graphon bounds
and the nonpositive quadratic expression are separate steps; this scalar
estimate does not establish them by itself.

## PS-006 — nonnegative surrogate codegrees without square roots

**Statement.** Suppose $0\le\lambda\le m$ and
$\lambda\psi^2\le2d-m$. Then
$$
\lambda^2|\psi|\le md,
\qquad c_\pm:=md\pm\lambda^2\psi\ge0.
$$
No separate assumption on d or the sign of ψ is needed.

**Complete replacement proof.** Put $s=|\psi|$. Multiply the diagonal
inequality by m≥0 and use the following polynomial identity:
$$
\begin{aligned}
2(md-\lambda^2s)
&\ge m^2+m\lambda s^2-2\lambda^2s\\
&=(m-\lambda)(m+\lambda)
  +\lambda(m-\lambda)s^2+\lambda^2(s-1)^2\ge0.
\end{aligned}
$$
Every term on the final line is nonnegative. Thus
$c_\pm\ge md-\lambda^2|\psi|\ge0$. ∎

**Use in the manuscript.** In the approximate Euler-equation part of
`lem:rowreduction`, substitute $m=\int U$, $d=d(x)$,
$\lambda=\lambda_0$ and $\psi=\psi_0(x)$. The spectral bounds
$0\le\lambda\le m$ and $\lambda\psi(x)^2\le2d(x)-m$ give the hypotheses
almost everywhere. This replaces only the AM–GM chain involving
$m^{3/2}\lambda^{1/2}|\psi|$; it does not replace the diagonal or spectral
bounds that supply those hypotheses.

It makes the needed domain of the exponential estimate explicit: both
$C_U$ and $c_\pm$ are nonnegative, so for μ≥0,
$$
|e^{-\mu C_U}-e^{-\mu c_\pm}|\le\mu|C_U-c_\pm|.
$$
Averaging this inequality over either block then gives the asserted μ times
its codegree-error bound.

**Lean correspondence.**
[`ExponentialRowEstimate.lean`](../lean/SparseLowerTail/Section07/ExponentialRowEstimate.lean):
`surrogate_codegree_bound` proves the scalar statement with exactly the
hypotheses above; `centered_surrogate_codegrees_nonneg` applies it to an
actual graphon's centered-kernel spectral expansion.
`abs_exp_neg_mul_sub_le` and `setAverage_exp_equation_error` prove the
exponential and averaging steps. No additional classical or numerical input
is used in this replacement.

## How to maintain this note

For each new simplification, retain its PS identifier, list the stable paper
label, state every hypothesis, write the complete mathematical argument, and
link the compiled Lean declaration. Record whether it replaces an entire
proof or only one step. Keep proposals separate from checked replacements.
