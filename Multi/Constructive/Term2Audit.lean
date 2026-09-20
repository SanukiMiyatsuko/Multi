import Multi.term2
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- This module only checks dependencies; it supplies no proofs to Multi.term2. -/

#print axioms T.NF_is_wellfounded
#print axioms T.OT_is_NF
#print axioms T.OT_is_wellfounded

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut count : Nat := 0
  for modName in env.header.moduleNames do
    if (`Multi.OCF).isPrefixOf modName || (`Mathlib).isPrefixOf modName then
      throwError "Unexpected import in the constructive proof: {modName}"
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`Multi).isPrefixOf modName then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "{name} depends on the disallowed axiom {ax}"
        count := count + 1
  logInfo m!"Checked {count} project declarations: only propext and Quot.sound are permitted."
