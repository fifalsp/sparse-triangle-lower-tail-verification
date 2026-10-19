# Proof issues and remaining verification gaps

Updated 2026-10-19. **No mathematical error in the paper has been established
by the checks recorded here. The main theorem is not yet formally proved.**
A successful Lean build verifies the encoded statements under their explicit
hypotheses; it does not by itself establish fidelity to every manuscript claim.

| Stable label | Kind | Current finding / required work |
| --- | --- | --- |
| `prop:cover`, `prop:family` | Missing formal proof | Python/Arb reports are available, but full-domain positivity and exact zero sets have not been converted to Lean proofs. These are internal obligations. |
| `prop:critical` | Conditional assembly | The graphon deduction now compiles, conditional on the cover and apex certificate. No result may silently retain those hypotheses in a claimed completed main theorem. |
| `thm:rigidity`, `thm:twowell` | Missing formal proof | Full insertion lemma and scalar two-well coercivity now compile. The functional coercivity bridge and local rigidity remain. |
| `cor:open`, `cor:seed` | Missing formal proof | Depend on local rigidity and the appropriate compactness/limit arguments. |
| `thm:smalltail` | Missing formal proof | Full scalar penalized classification and supporting-range data now compile. The latter uses the explicit KP26 input. Every minimizer satisfies the mean-zero quadratic inequality; graphon equality rigidity remains. |
| `lem:cut` | Partial translation / infrastructure | Actual norm and bijective distance are defined. Classical compactness is currently the weaker vertex-map consequence of the paper's bijective version. Pseudometric identities are proved for actual graphons. General pullback zero-distance uses an explicit classical L¹ approximation input. Weighted test bound remains under development. |
| `lem:relabelB` | Explicit classical dependency | Partition-to-pullback equivalence is proved using the finite nonatomic CDF transport hypothesis, precisely recorded in ASSUMPTIONS.md. It does not assert invertibility of the CDF map. |
| `lem:zc` | Alternative proved argument | Lean uses a compact-superlevel crossing argument instead of the paper's isolated finite-zero-set argument. This is a proof-route change, not evidence of a manuscript error. |

The full cover certificate still requires a checked subdivision/coverage argument,
not merely a digest of accepted numerical boxes. The apex also requires a checked
exact tangency solution and its Taylor bounds. Neither obligation has been
reclassified as external.

New suspected errors should be recorded with the exact statement, counterexample
or failed mathematical inference, and resolution status. A tactic failure alone
is not evidence of a mathematical error. Check the versioned proof map for exact
completed declarations and source statement/proof fingerprints.
