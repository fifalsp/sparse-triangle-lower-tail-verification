# Shorter proofs found during formalization

Updated: 2026-10-20. This is a companion to the manuscript, not an edit to it.
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
| PS-007 | `prop:structural`, Step 4 | Direct stationary-row coercivity closes actual small-tail bipodality | Lean checked; no insertion-minimality hypothesis for the row comparison |
| PS-008 | `prop:family`, local AAA case | Factored Hessian reduces the full parameter range to five interval leaves | Lean checked; local cube only |
| PS-009 | `s5:tangency`, `prop:cover` | One common determinant solves all six fan tangency systems | Lean checked; tangency only |
| PS-010 | `lem:discrete`(b) | Balanced finite color copies replace the midpoint and bad-cell estimate | Lean checked; every vertex count, same classical inputs |

## Compact outline of the final argument

The following **conditional outline is Lean checked** in
[`ContinuationAssembly.lean`](../lean/SparseLowerTail/Section08/ContinuationAssembly.lean),
with the discharged small-target and parameter-range inputs assembled in
[`FiniteCertificateAssembly.lean`](../lean/SparseLowerTail/Section08/FiniteCertificateAssembly.lean).
It follows the paper and makes the remaining work explicit; it is not a new
unconditional proof. Two internal statements remain to be discharged:

1. **Critical classification** (`prop:critical`), reduced elsewhere to the
   cover and apex certificates (`CriticalClassification`). The actual twelve-cell
   geometric coverage and all support cutoffs are now proved; the remaining
   work here is the nonlinear inequalities at the vertices/apexes, including
   the required equality cases.
2. **Compact intermediate certificate**: nonnegativity and the allowed-pattern
   zero set on the explicit compact box, for branch-log parameter
   3.9 ≤ L ≤ 9.5 (`CompactFamilyCertificate`). The inclusion of the actual
   intermediate branch parameters in this interval is now proved by
   `middle_branch_log_range`, and the analytic tail beyond the compact box
   is already assembled.

**Small-target classification is now proved** in
[`SmallTailAssembly.lean`](../lean/SparseLowerTail/Section07/SmallTailAssembly.lean),
`smallTarget_classification`: among all graphons, minimizers are exactly
balanced graphons with the branch values for 0 < r ≤ r₋. Its explicit inputs
are the recorded KP26 penalized reduction and the classical sampling and
positive-kernel spectral theorems. In particular, `SmallRangeClassification`
is no longer an unfinished internal hypothesis of the latest assembly.

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

Exact latest declaration: `Section08.mainTheorem_of_finite_certificates`.
It takes the named external/classical parameters `KP26PenalizedReduction`,
`UniformSampling`, `PositiveKernelSpectralTheorem`,
`ClassicalDyadicL1Approximation`, `ClassicalGraphonCompactness`,
`ClassicalPullbackApproximation`, and `ClassicalTriangleCounting`.
These are distinct from the two unfinished internal inputs above. The
assembly does **not** mean that `thm:main` is finished.

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

## PS-007 — small-tail rigidity directly from the row equations

**Manuscript anchor and scope.** This replaces Step 4 of
`prop:structural` in the proof of `thm:smalltail`. Together with the already
checked Steps 1–3 and the measurable row criterion in Step 5, it now closes
the actual small-target bipodality assertion. It is a different coercivity
regime from PS-003: the partition need not be balanced or close to balanced,
and no approximation to a fixed nonconstant balanced graphon is assumed.

**Precise statement.** Let U be a measurable symmetric graphon on a
probability space, let P be measurable, let μ≥18, and put
$a=e^{-0.27\mu}$. Assume
$$
0\le U\le a\quad\text{a.e. on }P^2\cup(P^c)^2,
\qquad 0\le U\le1\quad\text{a.e. everywhere}.
$$
Let v,w be measurable profiles with a common lower bound ℓ>0, satisfying
$$
\ell\le v,w\le1\quad\text{a.e.},\qquad
v,w\le a\quad\text{a.e. on }P,
$$
and suppose their actual row equations hold almost everywhere:
$$
\log v+\mu T_Uv=0,\qquad \log w+\mu T_Uw=0,
\qquad (T_Uv)(x)=\int U(x,y)v(y)\,dy.
$$
Then v=w almost everywhere. There is no hypothesis that these profiles
minimize an insertion functional. The assertion also permits |P|=0 or 1;
positive masses are needed later when extracting the two row types.

**Complete replacement proof.** Set f=v−w, p=|P|, and
$$
X=\left(\int_P f^2\right)^{1/2},\qquad
Y=\left(\int_{P^c} f^2\right)^{1/2},
\qquad Q_U(f)=\iint f(x)U(x,y)f(y)\,dx\,dy.
$$
For any 0<s,t≤b, integration of the derivative 1/u gives
$$
(s-t)(\log s-\log t)\ge\frac{(s-t)^2}{b}.
$$
Apply this with b=a on P and b=1 on its complement. Subtract the two row
equations, multiply by f, and integrate. All quantities are integrable:
the profiles are bounded, their logarithms are bounded by the common
positive lower bound, and U is bounded. Fubini gives
$$
a^{-1}X^2+Y^2
\le\int f(\log v-\log w)
=-\mu Q_U(f).
\tag{1}
$$
Let L=∫_P|f| and H=∫_{P^c}|f|. Since U is nonnegative and obeys the stated
block bounds,
$$
Q_U(f)\ge-a(L^2+H^2)-2LH.
$$
Cauchy–Schwarz gives L≤√p X and H≤√(1−p) Y. Consequently,
$$
Q_U(f)\ge-apX^2-2\sqrt{p(1-p)}XY-a(1-p)Y^2.
\tag{2}
$$
Combining (1) and (2) yields
$$
AX^2-2BXY+CY^2\le0,
\qquad
A=a^{-1}-\mu ap,\quad B=\mu\sqrt{p(1-p)},\quad
C=1-\mu a(1-p).
\tag{3}
$$
By PS-005, $a^{-1}>\mu+\mu^2/4$, so μa<1 and C>0. Moreover,
$$
\begin{aligned}
AC-B^2
&=a^{-1}-\mu(1-p)-\mu ap+\mu^2p(1-p)(a^2-1)\\
&\ge a^{-1}-\mu-\mu^2/4>0.
\end{aligned}
$$
Multiplying (3) by C and completing the square gives
$$
0\ge(CY-BX)^2+(AC-B^2)X^2\ge0.
$$
Thus X=Y=0, and f=0 almost everywhere. ∎

**Application to the actual small-target minimizer.** Let ψ be the leading
centered-kernel eigenfunction, put P={ψ≥0}, and let μ be the actual Euler
multiplier. The proved small-parameter bound gives μ≥18.6. Steps 1–2 give
opposite-block row average >0.775. Step 3 then gives, for almost every pair
in the same block,
$$
C_U(x,y)>0.498\cdot(2\cdot0.775-1)>0.27,
\qquad U(x,y)=e^{-\mu C_U(x,y)}\le e^{-0.27\mu}.
$$
The actual Euler equation also gives U≥e^(−μ)>0 almost everywhere because
0≤C_U≤1. By Fubini, choose a common conull set of row indices on which the
row equations, these upper and lower bounds, and row measurability all
hold. Two rows indexed by P then meet the precise hypotheses above, so
they coincide almost everywhere. Apply the same argument with P replaced
by its complement for the other class; the graphon envelope is unchanged
under this replacement.

Both block masses are positive: the proved spectral mass estimate and
certified parameter bound give
$$
|P|,|P^c|\ge\frac1{2M^2}>0.4987.
$$
The measurable row criterion, using symmetry of U, therefore gives three
constants a₀,d₀,b₀∈[0,1] with U equal almost everywhere to the corresponding
two-block kernel. This is actual bipodality on a measurable partition, not
an optimization restricted to bipodal candidates. Balancedness and the
identification of these values with the scalar branch are subsequent
classification steps.

**Null sets and sign convention.** The definition P={ψ≥0} makes P and Pᶜ
an exact measurable partition before any zero-set assertion is needed.
The row separation argument separately proves ψ≠0 almost everywhere, so
this convention agrees modulo null sets with the manuscript's positive
and negative sign blocks. The proof does not divide by a potentially zero
mass: positivity is established before conditional averages and before
representative rows are selected. No choice of representatives of U is
claimed to satisfy all bounds pointwise; each use of a row equation or cap
is made on the common conull set supplied by Fubini.

**Lean correspondence.**
[`SmallRowRigidity.lean`](../lean/SparseLowerTail/Section07/SmallRowRigidity.lean):
`rowQuadratic_lower_envelope`, `rowQuadratic_lower_blockcap`, and
`small_stationary_rows_eq` prove the precise statement above. This generic
row-uniqueness argument has no external theorem parameter.
[`RowSeparation.lean`](../lean/SparseLowerTail/Section07/RowSeparation.lean)
proves `smallTarget_row_means_separate` and
`smallTarget_oppositeBlock_means`;
[`SameBlockCap.lean`](../lean/SparseLowerTail/Section07/SameBlockCap.lean)
proves `smallTarget_sameBlock_codegree` and `smallTarget_sameBlock_cap`.
[`SmallTargetBipodal.lean`](../lean/SparseLowerTail/Section07/SmallTargetBipodal.lean),
`smallTarget_isBipodal`, combines these with
`Section06.bipodal_of_row_class_eq` and concludes
`∃ c a d b, IsBipodal U c a d b` for every actual minimizer at
0<r≤smallTarget.

The last declaration takes the recorded KP26 penalized reduction, classical
sampling, and an actual centered-kernel spectral expansion as explicit
inputs. The expansion is supplied separately by the recorded generic
classical spectral theorem. No row-separation estimate, block cap,
coercivity inequality, or bipodality assertion is assumed. The build and
selected declaration audits passed; `#print axioms` lists only
`propext`, `Classical.choice`, and `Quot.sound`. This audit does not discharge
explicit classical input propositions or establish the remaining
intermediate and critical certificate arguments.

**Editorial use.** Replace the interpolation paragraph in Step 4 by (1),
then retain the existing blockwise quadratic estimate and determinant
argument (or use PS-005 for the scalar exponential estimate). At the start
of the structural proof, include the row Euler equation and positive lower
bound in the list of properties holding outside N. Its use of (F3) to
compare insertion values is then unnecessary for this structural step;
other uses of the insertion result elsewhere in the manuscript are
unaffected.

## PS-008 — Five interval leaves for the full local AAA family

**Stable paper link:** `prop:family`, local AAA portion of Appendix A.3
(`appA3:hess` / `appA3:compact`). This is a simplification of one numerical
subproof, not a proof of the entire family certificate.

**Statement.** Let z>0, L=−log z in [3.9,9.5], and let p=(qA,qA,qA) be the
moving all-equal contact in logarithmic coordinates. For every q satisfying
max_i |q_i−p_i|≤1/10, Phi_z(q)≥0, and equality holds exactly when q=p.

**Argument.** Set x_i=exp(−q_i), A=mu*c4, and
G=x_0*x_1*x_2*(1+2*A−A*(q_0+q_1+q_2)). The actual Hessian entries are

```
H_ii = x_i*(c1+c2*(2−q_i)+c4*((q_i−2)^2−2))
       +mu*c3*x_i*sum_{j≠i} x_j + G,
H_ij = mu*c3*x_i*x_j + G  (i≠j).
```

This follows from the differentiated expression using
(q_i−2)^2−2=q_i^2−4*q_i+2 and cancelling x_i from the sum of three
exponentials. The factored expressions avoid needless interval dependence.
Subdivide the L interval at 4.25, 4.6, 5.3, and 6.7. On each of these five
closed intervals, exact exponential endpoint bounds enclose the actual
parameter coefficients and every coordinate in the moving radius-1/10 cube.
The generated Lean file checks strict positive diagonal-dominance margins
for the enclosed symmetric Hessian (identity congruence). Thus vᵀH(q)v>0
for every nonzero v, throughout that cube and for every permitted L.
There are no gaps at the four shared subdivision endpoints.

The contact identities give Phi_z(p)=0 and grad Phi_z(p)=0. For q≠p in the
cube, its segment from p remains in the cube by convexity. The function
f(t)=Phi_z(p+t*(q−p)) has f(0)=f'(0)=0 and f''(t)>0 for t in [0,1].
Consequently f'(t)>0 for t>0 and f(1)>0. The case q=p is the contact
identity. This proves both nonnegativity and the exact local zero set.

**Checked implementation:**
[`FamilyLocalFactoredIntervals.lean`](../lean/SparseLowerTail/Section08/FamilyLocalFactoredIntervals.lean)
proves the algebraic bridge;
[`FamilyAAACover.lean`](../lean/SparseLowerTail/Section08/FamilyAAACover.lean)
contains the five exact checks and
`FamilyAAACover.local_nonnegative_and_unique_zero`.
The generated rational data are proposals; Lean checks their validity with
`decide +kernel`. No external mathematical inputs are used for this local
result. The mixed-contact neighborhood and the global exterior still need
separate certificates.

## PS-009 — One determinant for all six fan tangency systems

**Stable paper links:** `s5:tangency`, the tangency paragraph of `app:cover`,
and the coefficient construction in `prop:cover`. This proves the exact
coefficient construction; positivity remains a separate obligation.

Write R(theta,lambda) for the four residuals: the AAA value, its first
logarithmic derivative, and the two inequivalent ABB derivatives. Each is
linear jointly in theta and lambda, since the original certificate is
linear in those parameters and differentiation preserves linearity. Let
E_j be the coefficient basis vectors at positions 0,2,3,4, and set
M_ij=R(E_j,0)_i. For the published fixed coefficient vector b_K (zero in
those four positions), the required correction x therefore satisfies

```
R(b_K + sum_j x_j E_j, lambda_K)
    = R(b_K,lambda_K) + M x = 0.
```

The matrix M is independent of K and lambda_K: only the right-hand side
changes. Bounds on the actual nine primitive constants give bounds on its
sixteen entries. Exact interval arithmetic then encloses det M in
[5186330326774856, 5186330397267159]/2^60, which is strictly positive.
Thus Cramer's rule gives a unique correction for every one of the six fan
rows. Adding this correction preserves every fixed coefficient, and the
four previously unspecified coefficients are the exact Cramer values.

The already proved weighted identity
Psi(AAA)+3*Psi(ABB)=0 gives the second zero value from the first.
Coordinate symmetry makes all three AAA derivatives equal and the two
repeated-coordinate ABB derivatives equal. Hence the four residual
equations imply zero value and all three logarithmic derivatives at both
contacts. This is exactly the coordinate formulation used in the Appendix;
it does not assert any Hessian or global positivity estimate.

**Lean checked:**
[`ApexTangencyDeterminant.lean`](../lean/SparseLowerTail/Section05/ApexTangencyDeterminant.lean)
and [`ApexFanTangency.lean`](../lean/SparseLowerTail/Section05/ApexFanTangency.lean).
The determinant proof uses separately checked entry enclosures so the
symbolic expressions need not be replayed at every determinant occurrence.
No external mathematical premise is used for these statements.

## How to maintain this note

For each new simplification, retain its PS identifier, list the stable paper
label, state every hypothesis, write the complete mathematical argument, and
link the compiled Lean declaration. Record whether it replaces an entire
proof or only one step. Keep proposals separate from checked replacements.


## Local apex certificate: compact implementation record

All twelve contact cubes in the six fan cells are now handled by one proof
schema, implemented in `apexPhi_local_of_interval_taylor` in
`SparseLowerTail.Section05.ApexTaylorIntervals.lean`. This follows
`lem:taylor`; it is not an additional mathematical simplification or a new
proof of global positivity.

For each exact fan coefficient vector, let `ell` be a positive rational and
let `C[i,j,k]` bound the absolute third partial throughout the published cube.
Certify the symmetric center Hessian minus `ell I` by a rational congruence,
and check `delta * sum(C) < 3 ell`. Along the segment from the contact to q,
the third derivative is bounded in absolute value by
`sum(C) * delta * ||q-contact||_2^2`. Taylor's theorem and exact zero value
and gradient give

`Phi(q) >= (ell/2 - delta*sum(C)/6) * ||q-contact||_2^2`.

Thus the entire cube is nonnegative and the contact is its only zero.
The twelve numerical checks use the full published radii. Everything outside
these neighborhoods remains a separate certificate obligation.


### 2026-10-19 — one rational chain rule for all family parameter derivatives

The seven coefficient formulas depend on the three primitive variables
`z = exp(-L)`, `L`, and `b = exp(-2*z*L/(1-z)^2)`. Their velocity is rational
in those same variables. Rather than prove separate derivative formulas for
every coefficient and every order, `RationalExprCalculus` proves one chain
rule by induction on expressions. A successful interval evaluation also proves
every denominator is nonzero; repeated differentiation therefore remains
within the existing checked evaluator.

`FamilyParameterTaylor.phi_parameter_taylor_lower` then combines the
coefficients with the fixed-q weights **before** taking the absolute remainder
bound. It retains the signed second derivative and handles L on either side
of the center. This follows the computation in `verification/family/core.py`
while reducing the analytic proof to one reusable theorem. A sample checks
all 28 coefficient/order combinations on [39/10,2503/640].

Scope: this simplifies the formal verification architecture, not the
mathematical statement of Proposition `prop:family`. The full q-dependent
exterior certificate and its complete cover still need to be discharged.


### 2026-10-19 — separate the exterior estimate into reusable scalar bounds

`FamilyGradientParameter` identifies each actual q-gradient as a weighted sum
of the same seven coefficient functions, and proves its parameter variation
using a second-order remainder. `QuadraticAxisBounds` proves the three choices
made in `compact_test`: the interval-safe quadratic bound, the unconstrained
positive-curvature minimum, and the sharper interval-endpoint value when the
stationary point lies outside the allowed interval. The endpoint test needs a
**lower bound** on the gradient magnitude as well as the usual upper bound.

`familyPhi_exterior_lower` assembles these pieces using the actual Hessian
along the q segment. Diagonal curvature keeps its sign; only off-diagonal
terms are bounded in absolute value. Its input is explicit value/gradient/
Hessian enclosures, not an assumption of the desired positivity. This keeps
the analytic argument short while leaving the finite numerical data and
coverage obligations visible. No change to the paper's mathematical claim is
proposed, and no complete exterior certificate is claimed yet.


### 2026-10-19 — finite exterior data now imply the actual analytic bounds

`FamilyTaylorData` packages the whole parameter interval, a certified parameter
center, three q-center exponential certificates, derivative tables, and a
parameter width. Its validity checks are exact rational or dyadic computations.
The soundness theorem derives the actual value lower bound and both gradient
magnitude bounds; the center is checked to lie inside the interval, and the
width is checked to cover both directions.

`FamilyExteriorLeaf` adds the whole q-box, Hessian interval calculation,
coordinate radii, quadratic choices, and a positive rational margin. Its
`margin_le` theorem proves the margin bounds the actual certificate everywhere
in the box. The sample `FamilyExteriorSmoke` checks this entire pipeline on
L ∈ [39/10,2503/640], qᵢ ∈ [99/100,101/100], with margin greater than 1/1000.
The full subdivision is not generated or proved by this sample.

This separation makes subsequent numerical searches untrusted proposal
programs: a proposed box must still instantiate the same finite validity
checks, and the final tree must separately prove coverage.


### Compact family: one conclusion for all leaves (`prop:family`)

The global assembly can use a single leaf conclusion: Phi is nonnegative,
and a zero has one of the prescribed AAA or ABB patterns. Strictly positive
Taylor leaves satisfy the zero implication vacuously; local contact leaves
use their unique-zero theorem. Sorting needs no separate strict-order case:
permutations preserve Phi and the allowed patterns, even when coordinates
coincide. `SparseLowerTail.Certificate.compactFamilyCertificate_of_ordered`
formalizes this reduction.

`compactFamilyCertificate_of_table` in the same namespace
then reduces the whole compact family to a single exact subdivision table.
Empty leaves are allowed only when an upper coordinate bound is strictly
below the next coordinate's lower bound; equality is retained in the domain.
For moving contacts, containment uses the upper contact endpoint to constrain
the box's lower side, and the lower contact endpoint for its upper side.
This direction guarantees containment for every parameter in the interval.

These are checked reductions, not a discharge of the numerical premises.
The 64,646-leaf exterior proposal still needs full Lean replay, and the ABB
local result remains an explicit internal obligation. The reduction preserves
the paper's complete conclusion rather than replacing it by positivity alone.


### Critical classification: a precise finite interface (`prop:cover`, `prop:critical`)

`SparseLowerTail.Section05.criticalClassification_of_ordered_jobs` now takes
exactly the full sorted-domain conclusions for the 36 nonapex jobs and six
apex fans, plus the four named classical inputs already used by the paper.
The proof derives the complete cover from the actual cell/vertex inventory.
Every nonapex vertex has a checked job index; an exceptional apex is either
in a fan cell or already accounted for by that inventory. No additional
geometric or support assertions need to be supplied by the numerical program.
One fan's zero-pattern conclusion then gives the critical rigidity input.

This is a simplification of the proof interface. All 42 full-domain numerical
conclusions still need Lean proofs; successful search proposals and individual
boxes do not meet this requirement. The wider endpoint checker repairs the
B1/B2 range restriction without changing the certificate formulas.

## PS-010 — Finite color copies for the discrete upper limit

A fixed K-block graphon can be approximated for the two observables needed
here by balanced copies of its colors. Write n = K m + d with d < K. Use m
complete batches containing every color once and assign the remaining d
vertices to color zero. Every empirical color mass tends to 1/K. Exact pair
and triple color-sum formulas then give convergence of the entropy and
triangle observables for every n.

Deleting diagonal edges increases normalized sparse entropy by at most 1/n
and decreases the triangle count. A strictly feasible block competitor
therefore gives feasible finite vectors for all sufficiently large n,
uniformly in p. The uniform Bernoulli entropy bound supplies the correction
p/(2(1-p)), which vanishes as p tends to zero. This proves the manuscript's
upper limit without tracking the locations of coarse-cell boundaries.

The finite coloring, its exact sums, both limits, diagonal bounds, eventual
feasibility and final sequence argument are proved in
[DiscreteComparison.lean](../lean/SparseLowerTail/Section03/DiscreteComparison.lean)
and its imports. The named classical inputs are the same dyadic approximation,
compactness and triangle-counting inputs used for graphon existence. The
[combined check](../lean/data/discrete-comparison-check.json) includes both
parts of the discrete lemma and all 70 declaration audits.

## PS-011 — Use the generic KS23 bounds before taking the limit

The rate deduction applies KS23 Theorems 5 and 6 to the triangle hypergraph
and retains their additive constants. Dividing by n²p/2 makes these constants
vanish in the sparse regime. The discrete variational limit supplies each
fixed perturbation bound, and continuity of V lets the perturbation shrink
to zero. This avoids a separate finite-size absorption argument while
proving the same probability asymptotic.

The generic inputs are explicit hypotheses. The triangle coordinates,
variational identification, codegrees and both limiting steps are proved in
[LowerTailRate.lean](../lean/SparseLowerTail/Section03/LowerTailRate.lean)
and its imports. The [check record](../lean/data/lower-tail-rate-check.json)
audits all 23 new public theorems. This closes part (a) of `thm:reduction`;
part (b) remains.


## PS-012 — Two signed tests for vertex rounding

For a balanced sign g and its cell average c, every step matrix M has
identical tests against g⊗g and c⊗c. For B = ℓ + μg⊗g, these tests are
μ and μq², where q = ∫c² = ∫gc and ∫c = ∫g = 0. The signed cut estimate
bounds each error by 4δ, so |μ|(1−q²) ≤8δ. Since 0≤q≤1, this implies
|μ|(1−q) ≤8δ.

Rounding each c_i to its sign improves correlation with g because
c_i²≤|c_i|. Thus the sign L¹ error is at most 1−q, its cardinality
imbalance is at most n(1−q)/2, and its rank-one kernel error is at most
2|μ|(1−q). These bounds imply the manuscript's constants 16 and 33
(the cut estimate obtained here is actually 17δ). This avoids constructing
an L² orthogonal projection or assuming cut-norm contraction. All cell
integral identities and signed-test bounds are proved in Lean.

Lean: `Section03.SignedCut`, `PartitionTests`, `CellAverages`, `RankOneTests`,
`SignRounding`, `RankOneRounding` and `Rounding`; 35 audited public theorems.
