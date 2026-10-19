# Formalization scope and assumptions

Updated 2026-10-19 following the authors' explicit instructions: assume cited
external theorems and standard classical results; verify the paper's own new
arguments. The final deliverable is therefore a **formal proof relative to
explicit external/classical inputs**, not a reproof of all mathematics used by
the paper.

We retain three different statuses:

1. **Proved here:** Lean proof terms checked using mathlib and any named inputs
   visible in the theorem's type.
2. **Assumed external/classical:** an exact statement with a stable identifier,
   source reference and explicit role in the proof. Such an input is passed as
   a hypothesis; it is not silently installed as a global axiom.
3. **Still to prove:** an obligation in this paper. Having a definition, a
   numerical report, or a conditional theorem does not discharge it.

The axiom audit still allows only `propext`, `Classical.choice`, and `Quot.sound`.
An assumed theorem appears as an ordinary hypothesis of the final result; the
audit alone cannot certify that the hypothesis has been proved. This file and
the final theorem's type provide that separate provenance information.

## Explicitly encoded external input

### `external:KP26:1.6`

- Reference: KP26, Theorem 1.6, with the specialization justified in the paper
  immediately before equation `eq:KP`.
- Exact Lean proposition:
  `SparseLowerTail.Section07.KP26PenalizedReduction` in
  [`ExternalReduction.lean`](SparseLowerTail/Section07/ExternalReduction.lean).
- Meaning: for γ > 0, a minimizing balanced pair for F + γt gives a lower bound
  for F(U) + γt(U) for **every graphon U**.
- Status: **assumed external**, never asserted by an axiom or claimed proved.
- Proved consequences: scalar penalized minimizer existence (independent of
  KP26), transfer to constrained optimality at a supported target, the value
  identity, and the active constraint/penalized optimality of every constrained
  minimizer at that target.
- Remaining internal obligations: identify the supporting pair and range
  r ≤ r₋ using the paper's scalar penalized analysis; prove its equality-case
  rigidity. The transfer lemma does not by itself establish `prop:smalldata`
  or `thm:smalltail` in full.

## Classical infrastructure eligible to be assumed when needed

These inputs have not all been encoded yet. Their exact Lean types must be
written and reviewed at the point of use.

| Stable identifier | Classical result and paper location | References in the paper |
| --- | --- | --- |
| `classical:graphon-cut-compactness` | Sequential compactness modulo measure-preserving relabelings; `lem:cut`(c). | BCLSV08 Proposition 3.6; LS07 Theorem 5.1; Lov12 Theorem 9.23. |
| `classical:cut-distance-representation` | Coupling/relabeling descriptions of cut distance and their equivalence; `lem:cut`(d). | BCLSV08 Lemma 3.5. |
| `classical:counting-lemma` | Continuity of triangle density in cut norm; `lem:cut`(b). | Lov12 Lemma 10.23. |
| `classical:measure-analysis` | Standard Fubini, dominated convergence, Jensen, compactness, differentiation, and inverse-function results. | Use existing mathlib theorems where available; add a precise explicit input only when necessary. |

The paper's own Euler–Lagrange/vertex arguments, branch and crossing analysis,
rigidity, boundary comparison, certificate verification, and final assembly
remain proof obligations. They are not reclassified as classical merely because
proving them in Lean is difficult. The numerical certificates remain part of the
new argument and are not covered by the permission to assume external theorems.

## Changing the manuscript

[`proof-map.json`](proof-map.json) uses LaTeX labels as identifiers. Displayed
numbers are optional historical metadata. Each entry has a normalized statement
fingerprint and, when present, a fingerprint of its adjacent proof.

After exporting a revised draft, run from the repository root:

```sh
python3 tools/check_manuscript_map.py /path/to/revised/arxiv_v1.tex
```

Intro edits and automatic renumbering leave the mapped statements unchanged.
A changed statement, changed proof, missing label or renamed label requires
review. The checker never updates proof status or accepts a new baseline.
Update the corresponding Lean declaration and affected dependents, rebuild and
audit, then deliberately update the map baseline and progress log. Keep stable
labels through revisions where possible; if a label is renamed, record its old
name as an alias in the map rather than silently treating it as a new theorem.

This is a focused textual tracker, not a full TeX parser or semantic-equivalence
checker. Changes to shared macro definitions or unmapped statements also require
manual review. A clean comparison does not prove that a revised paper is correct.
