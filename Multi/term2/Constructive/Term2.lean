import Multi.term2.Term2Consequences
import Multi.term2.Constructive.Term2Closure

namespace T.Constructive

/-- Constructive well-foundedness from relative fundamental-sequence reductions. -/
theorem NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 :=
  normalForms_wellFounded

theorem OT_is_NF (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z :=
  T.OT_is_NF_of_wellFounded NF_is_wellfounded s

theorem OT_is_wellfounded : WellFounded fun x y : T.OT => x.1 < y.1 :=
  T.OT_wellFounded_of_NF_wellFounded NF_is_wellfounded

end T.Constructive
