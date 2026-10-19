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
and its exact subdivision coverage are underway. This is one of 36 nonapex
jobs. The six apex jobs also need exact tangency and local/global bounds.
Neither obligation is an external assumption. Family interval coefficient
conversion and local Hessian/contact calculus are proved, but the actual
compact-domain numerical bounds remain.

New suspected errors should be recorded with the exact statement, counterexample
or failed mathematical inference, and resolution status. A tactic failure alone
is not evidence of a mathematical error. Check the versioned proof map for exact
completed declarations and source statement/proof fingerprints.
