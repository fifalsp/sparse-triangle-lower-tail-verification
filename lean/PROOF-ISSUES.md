# Proof issues and remaining verification gaps

Updated 2026-10-19. **No mathematical error in the paper has been established
by the checks recorded here. The main theorem is not yet formally proved.**
A successful Lean build verifies the encoded statements under their explicit
hypotheses; it does not by itself establish fidelity to every manuscript claim.

| Stable label | Kind | Current finding / required work |
| --- | --- | --- |
| `prop:cover`, `prop:family` | Missing formal proof | Python/Arb reports are available, but full-domain positivity and exact zero sets have not been converted to Lean proofs. These are internal obligations. |
| `prop:critical` | Conditional assembly | The graphon deduction now compiles, conditional on the cover and apex certificate. No result may silently retain those hypotheses in a claimed completed main theorem. |
| `thm:rigidity`, `lem:insertion`, `thm:twowell` | Missing formal proof | Local row variation, two-well coercivity and rigidity are still being formalized. |
| `cor:open`, `cor:seed` | Missing formal proof | Depend on local rigidity and the appropriate compactness/limit arguments. |
| `prop:pen`, `prop:smalldata`, `thm:smalltail` | Missing formal proof | Stationary, fold, tie and unique-crossing lemmas now compile; full penalized classification, supporting range and graphon equality rigidity remain. |
| `lem:cut` | Partial translation / infrastructure | Actual norm and bijective distance are defined. Classical compactness is currently the weaker vertex-map consequence of the paper's bijective version. Full pseudometric/relabeling facts remain under development. |
| `lem:relabelB` | Explicit classical dependency | Partition-to-pullback equivalence is proved using the finite nonatomic CDF transport hypothesis, precisely recorded in ASSUMPTIONS.md. It does not assert invertibility of the CDF map. |
| `lem:zc` | Alternative proved argument | Lean uses a compact-superlevel crossing argument instead of the paper's isolated finite-zero-set argument. This is a proof-route change, not evidence of a manuscript error. |

New suspected errors should be recorded with the exact statement, counterexample
or failed mathematical inference, and resolution status. A tactic failure alone
is not evidence of a mathematical error. Check the versioned proof map for exact
completed declarations and source statement/proof fingerprints.
