import Multi.Constructive.Term3Normal
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- This checks the proved foundations only. T.OT_is_wellfounded is still open.
#print axioms T.fund_lt_of_domain
#print axioms T.fund_ofNat_lt
#print axioms T.OT_lt_first_uncountable
#print axioms T.base_isNF
#print axioms T.dom_omega_properties

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`Multi).isPrefixOf modName then
        for ax in ← collectAxioms name do
          unless allowed.contains ax do
            throwError "{name} depends on {ax}"
        count := count + 1
  logInfo m!"Checked {count} foundation declarations; the target theorem is not included."
