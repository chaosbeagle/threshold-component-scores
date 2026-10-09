import ThresholdComponentScores
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if Name.isPrefixOf `ThresholdComponentScores name then
      count := count + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Kernel audit passed: {count} ThresholdComponentScores constants; only propext, Classical.choice, Quot.sound permitted."
