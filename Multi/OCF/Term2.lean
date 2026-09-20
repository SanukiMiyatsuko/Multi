import Multi.Term2Consequences
import Multi.OCF.Term2Interpretation

namespace T.OCF

/-- Classical well-foundedness through the ordinal collapsing interpretation. -/
theorem NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 := by
  apply Subrelation.wf (r := fun x y : T.NF => T.denote x.1 < T.denote y.1)
  · intro x y hxy
    exact T.denote_strict x.1 y.1 x.2 hxy
  · exact InvImage.wf (fun x : T.NF => T.denote x.1) _root_.OCF.Ordinal.lt_wellFounded

theorem OT_is_NF (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z :=
  T.OT_is_NF_of_wellFounded NF_is_wellfounded s

theorem OT_is_wellfounded : WellFounded fun x y : T.OT => x.1 < y.1 :=
  T.OT_wellFounded_of_NF_wellFounded NF_is_wellfounded

end T.OCF
