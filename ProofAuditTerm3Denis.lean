import Lean
import Multi.term3.Denis.RevisedDomains

/-! Audit the actual imported declarations, with no dependence on Term3.lean's
unfinished theorems. Run after `lake build Multi.term3.Denis.RevisedDomains`.
The ordinal model uses the existing classical ordinal library. The purely
syntactic correspondence module retains the stricter constructive axiom set.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    let mod := env.header.moduleNames[idx.toNat]!
    if (`Multi.term3).isPrefixOf mod && (info.isTheorem || info.isDefinition) then
      some (name, mod)
    else none
  for (name, mod) in names.mergeSort (fun a b => Name.quickLt a.1 b.1) do
    let axs ← collectAxioms name
    let constructive := mod == `Multi.term3.Term3Correspondence ||
      mod == `Multi.term3.Term3Syntax || mod == `Multi.term3.Term3Fundamental ||
      mod == `Multi.term3.Term3Normal
    unless axs.all (fun ax => ax == ``propext || ax == ``Quot.sound ||
        (!constructive && ax == ``Classical.choice)) do
      logError m!"Unexpected axioms in {name}: {axs}"
    if env.find? name |>.any (fun i => i.isTheorem) then
      let axNames := String.intercalate "," (axs.toList.map Name.toString)
      logInfo s!"VERIFIED|{name}|{mod}|{axNames}"
  logInfo m!"Audited {names.length} Term3 declarations; no sorryAx or new axioms."
