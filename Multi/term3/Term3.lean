import Multi.term3.Term3Fundamental
import Multi.term3.Term3Normal
import Multi.term3.Term3Syntax

open T

theorem NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 := sorry

theorem OT_is_NF (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z Z) Z Z Z := sorry

theorem OT_is_wellfounded : WellFounded fun x y : T.OT => x.1 < y.1 := sorry
