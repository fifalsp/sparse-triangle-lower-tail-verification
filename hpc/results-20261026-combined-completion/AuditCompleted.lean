import SparseLowerTail.CompletedReplays
import Lean.Util.CollectAxioms

/-! Fail if any declaration in our public namespace depends on an axiom other
than Lean's standard classical foundations. In particular this rejects sorryAx,
custom axioms, and native_decide's compiler-trust axioms. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  let mut theoremCount := 0
  let mut roots : Array Name := #[]
  for (name, info) in env.constants.toList do
    if (`SparseLowerTail).isPrefixOf name || name.toString.startsWith "_private.SparseLowerTail." then
      count := count + 1
      match info with
      | .thmInfo _ => theoremCount := theoremCount + 1
      | _ => pure ()
      roots := roots.push name
  -- Share the visited set across roots: imported proofs need traversal only once.
  let visit : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, audit) := (visit.run env).run {}
  for ax in audit.axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Unapproved axiom in project dependency closure: {ax}"
  if theoremCount == 0 then throwError "No project theorems were audited"
  logInfo m!"Axiom audit passed: {count} project declarations, {theoremCount} theorems; only propext, Classical.choice, Quot.sound allowed."
