# Proof issues and remaining verification gaps

Updated 2026-10-19. **No mathematical error in the paper has been established
by the checks recorded here. The main theorem is not yet formally proved.**
The latest assembly is `Section08.mainTheorem_of_finite_certificates`. Its two
internal hypotheses are `CriticalClassification` and `CompactFamilyCertificate`;
neither may be treated as a classical result. Small-range classification is proved.

A successful Lean build verifies the encoded statements under their explicit
hypotheses; it does not by itself establish fidelity to every manuscript claim.

| Stable label | Kind | Current finding / required work |
| --- | --- | --- |
| `prop:cover`, `prop:family` | Missing formal proof | Python/Arb reports are available. Actual twelve-cell geometry, all 179 curved-boundary checks and support cutoffs are proved. S1 vertex-0 positivity is proved in near-one/tail regions and a seventeen-leaf Taylor slab with exact coefficients. The family analytic tail is proved. Full-domain positivity and exact zero sets remain internal obligations. |
| `prop:critical` | Conditional assembly | The graphon deduction now compiles, conditional on the cover and apex certificate. No result may silently retain those hypotheses in a claimed completed main theorem. |
| `thm:rigidity`, `thm:twowell` | Resolved formal gap | Complete functional two-well theorem and full sequential local rigidity now compile. Local rigidity uses only the recorded classical sampling input. |
| `prop:stability`, `cor:open`, `cor:seed` | Stability/open resolved; seed conditional | Actual compactness, limit and local-rigidity assembly compiles. Openness uses only recorded classical inputs. The left seed still requires `CriticalClassification`, an internal obligation. |
| `thm:smalltail`, `prop:structural` | Resolved formal gap | Full unrestricted small-target classification now compiles, relative to the named KP26, sampling and spectral inputs. The exact relabeling formulation uses classical CDF transport. All row separation, same-block caps and equality rigidity are proved internally. |
| `lem:cut` | Partial translation / infrastructure | Actual norm and bijective distance are defined. Classical compactness is currently the weaker vertex-map consequence of the paper's bijective version. Pseudometric identities are proved for actual graphons. General pullback zero-distance uses an explicit classical L¹ approximation input. The sharp weighted test bound is now proved for arbitrary integrable kernels. |
| `lem:relabelB` | Explicit classical dependency | Partition-to-pullback equivalence is proved using the finite nonatomic CDF transport hypothesis, precisely recorded in ASSUMPTIONS.md. It does not assert invertibility of the CDF map. |
| `lem:zc` | Alternative proved argument | Lean uses a compact-superlevel crossing argument instead of the paper's isolated finite-zero-set argument. This is a proof-route change, not evidence of a manuscript error. |

The full nonlinear cover certificate still requires checked subdivisions covering
each logarithmic cube, not merely a digest of accepted boxes. This is separate
from the two-dimensional geometric cover, which is now fully proved. The first
128 leaves of the new 15,280-leaf S1 proposal have compiled; a complete replay
and its exact subdivision coverage remain unfinished. Bulk replay on the
desktop remains stopped to respect the storage constraint; the full S1 job
is now running on Yale Bouchet. This is one of 36 nonapex jobs. The six apex tangency systems are now solved exactly with a common checked
nonzero determinant. All twelve local contact cubes now have proved positivity
and exact zero classification at the published radii. The global apex bounds
outside those cubes still remain.
Neither obligation is an external assumption. Family interval coefficient
conversion and local Hessian/contact calculus are proved, but the actual
compact-domain numerical bounds remain outside the AAA neighborhood. The AAA
local result is now proved for all L in [3.9,9.5], on the closed logarithmic
cube of radius 1/10; the mixed-contact neighborhood and exterior are not
discharged by that result.

New suspected errors should be recorded with the exact statement, counterexample
or failed mathematical inference, and resolution status. A tactic failure alone
is not evidence of a mathematical error. Check the versioned proof map for exact
completed declarations and source statement/proof fingerprints.


Numerical formalization limitation (2026-10-19): direct interval evaluation
with the current apex primitive/solved-coefficient bounds fails to separate
zero at sampled rational points just outside five ABB contact cubes. This is
an interval-precision limitation, not a manuscript counterexample. The recorded
untrusted diagnostic is `data/apex-exterior-precision-diagnostic.json`; the
next remedy is sharper constant enclosures or a tangency-preserving evaluator.
No large apex subdivision should be treated as sufficient merely because its
spatial boxes are small.


### 2026-10-19: refined apex precision

The actual crossing bounds have now been propagated through all nine primitives,
the common matrix, all six right-hand sides, and all 24 solved coefficients,
with Lean kernel checks. The widest coefficient enclosure is below 4.77e-14.
All twelve previously recorded exterior diagnostic samples now have positive
Python interval lower bounds. This resolves the observed precision limitation
at those samples, not the full-domain certificate obligation. No manuscript
mathematical error or counterexample has been established.

### 2026-10-19: intermediate ABB replay scope

The original endpoint checker accepted only q≥0. The full ABB neighborhood
extends below zero at large L. This implementation restriction is resolved by
a proved extension to -16≤q≤16; the full root build and audit pass.

The full scaled-Hessian ABB subdivision is now proposed (108,452 leaves), and
its complete Python tree/enclosure/margin consistency check passes. Lean proves
the numerical-to-analytic checker, moving-contact enclosure and four-dimensional
coverage/assembly, plus two selected leaves. **The full leaf replay is missing.**
This does not establish the whole ABB neighborhood, nor the exterior family.
No mathematical counterexample or manuscript error was found in this work.

A monitoring step on Bouchet failed to create a cgroup with "Cannot allocate
memory". The scheduler subsequently still reported both S1 and F1 batch jobs
RUNNING, with no error in their batch stderr at that observation. The failed
monitor is not evidence that either certificate succeeded or failed; retain
and inspect the existing job IDs before any restart.


### 2026-10-19: exterior family scope

A complete 64,646-leaf exterior/contact proposal now passes exact Python
consistency checks. The zero-preserving ordered-to-unordered assembly is
proved in Lean, and 14 representative generated leaves plus one complete
subtree compile. These include each quadratic choice and each leaf type.
The full exterior replay and full ABB local theorem are still required;
`FamilyABBLocal` remains an explicit internal premise, not an allowed external
assumption. Source-generation errors found in the smoke test were repaired.
No new mathematical counterexample or manuscript gap was found.
