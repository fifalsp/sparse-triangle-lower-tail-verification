# Proof issues and remaining verification gaps

Updated 2026-10-19. **No mathematical error in the paper has been established
by the checks recorded here. The main theorem is not yet formally proved.**
The final assembly is now `Section08.mainTheorem_of_remaining_inputs`. Its three
internal hypotheses are `CriticalClassification`, `SmallRangeClassification`,
and `MiddleFamilyCertificate`; none may be treated as a classical result.

A successful Lean build verifies the encoded statements under their explicit
hypotheses; it does not by itself establish fidelity to every manuscript claim.

| Stable label | Kind | Current finding / required work |
| --- | --- | --- |
| `prop:cover`, `prop:family` | Missing formal proof | Python/Arb reports are available. Actual S1 vertex-0 positivity is proved in near-one/tail regions and a full Taylor box with exact coefficients. The family analytic tail is proved. Full-domain positivity and exact zero sets remain internal obligations. |
| `prop:critical` | Conditional assembly | The graphon deduction now compiles, conditional on the cover and apex certificate. No result may silently retain those hypotheses in a claimed completed main theorem. |
| `thm:rigidity`, `thm:twowell` | Resolved formal gap | Complete functional two-well theorem and full sequential local rigidity now compile. Local rigidity uses only the recorded classical sampling input. |
| `prop:stability`, `cor:open`, `cor:seed` | Stability/open resolved; seed conditional | Actual compactness, limit and local-rigidity assembly compiles. Openness uses only recorded classical inputs. The left seed still requires `CriticalClassification`, an internal obligation. |
| `thm:smalltail` | Missing formal proof | Full scalar penalized classification and supporting-range data now compile. The latter uses the explicit KP26 input. Mean-zero quadratic and spectral/degree/tail estimates are proved; the latter uses a precisely stated generic classical spectral theorem. Full row reduction, all small-parameter error bounds and scalar exclusion are now proved. Graphon equality rigidity remains. |
| `lem:cut` | Partial translation / infrastructure | Actual norm and bijective distance are defined. Classical compactness is currently the weaker vertex-map consequence of the paper's bijective version. Pseudometric identities are proved for actual graphons. General pullback zero-distance uses an explicit classical L¹ approximation input. The sharp weighted test bound is now proved for arbitrary integrable kernels. |
| `lem:relabelB` | Explicit classical dependency | Partition-to-pullback equivalence is proved using the finite nonatomic CDF transport hypothesis, precisely recorded in ASSUMPTIONS.md. It does not assert invertibility of the CDF map. |
| `lem:zc` | Alternative proved argument | Lean uses a compact-superlevel crossing argument instead of the paper's isolated finite-zero-set argument. This is a proof-route change, not evidence of a manuscript error. |

The full cover certificate still requires a checked subdivision/coverage argument,
not merely a digest of accepted numerical boxes. The full S1 vertex-0 search
proposal is now saved reproducibly, but only an initial full Taylor leaf has been replayed in Lean; full-tree replay and coverage remain. The apex also requires a checked
exact tangency solution and its Taylor bounds. Neither obligation has been
reclassified as external.

New suspected errors should be recorded with the exact statement, counterexample
or failed mathematical inference, and resolution status. A tactic failure alone
is not evidence of a mathematical error. Check the versioned proof map for exact
completed declarations and source statement/proof fingerprints.
