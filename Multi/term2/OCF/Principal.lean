import Multi.term2.OCF.Arithmetic

namespace OCF.Ordinal

universe u

noncomputable def principalStage (a : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => succ a
  | n + 1 => principalStage a n + principalStage a n

theorem principalStage_pos (a : Ordinal.{u}) (n : Nat) : 0 < principalStage a n := by
  induction n with
  | zero => exact lt_of_le_of_lt (zero_le a) (lt_succ_self a)
  | succ n ih => exact lt_of_lt_of_le ih (le_add (principalStage a n) (principalStage a n))

theorem principalStage_lt_succ (a : Ordinal.{u}) (n : Nat) :
    principalStage a n < principalStage a (n + 1) := by
  have h := add_lt_add_right (principalStage a n) (principalStage_pos a n)
  rw [add_zero] at h
  exact h

theorem principalStage_mono (a : Ordinal.{u}) {n m : Nat} (h : n ≤ m) :
    principalStage a n ≤ principalStage a m := by
  induction h with
  | refl => exact le_refl _
  | @step m h ih => exact le_trans ih (Or.inl (principalStage_lt_succ a m))

noncomputable def principalHull (a : Ordinal.{u}) : Ordinal.{u} :=
  sup (fun n : ULift.{u} Nat => principalStage a n.down)

theorem principalStage_le_hull (a : Ordinal.{u}) (n : Nat) :
    principalStage a n ≤ principalHull a :=
  le_sup (fun k : ULift.{u} Nat => principalStage a k.down) (ULift.up n)

theorem lt_principalHull (a : Ordinal.{u}) : a < principalHull a :=
  lt_of_lt_of_le (lt_succ_self a) (principalStage_le_hull a 0)

theorem principalHull_principal (a : Ordinal.{u}) : AddPrincipal (principalHull a) := by
  intro x y hx hy
  cases (lt_sup_iff _ x).mp hx with
  | intro n hn =>
    cases (lt_sup_iff _ y).mp hy with
    | intro m hm =>
      have hxk := lt_of_lt_of_le hn (principalStage_mono a (Nat.le_max_left n.down m.down))
      have hyk := lt_of_lt_of_le hm (principalStage_mono a (Nat.le_max_right n.down m.down))
      have hxy := lt_of_le_of_lt (add_mono_left (Or.inl hxk) y)
        (add_lt_add_right (principalStage a (max n.down m.down)) hyk)
      exact lt_of_lt_of_le hxy (principalStage_le_hull a (max n.down m.down + 1))

end OCF.Ordinal
