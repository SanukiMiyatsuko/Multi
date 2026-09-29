import Multi.term3.Denis.Sequences

/-! The first diagonal collapse: a semantic proof of the fundamental
sequence at psi_{I(0,0)}(I(0,0)). No identification with epsilon-zero is
assumed in this module. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def tower (s : Supply) : Nat → O
  | 0 => 0
  | n + 1 => psi s (I s 0 0) (tower s n)

theorem first_regular (s : Supply) : UncountableRegular (I s 0 0) :=
  regularIndex_regular s _ (Or.inl ⟨0, rfl⟩)

theorem first_mem_C (s : Supply) (a b : O) : C s a b (I s 0 0) :=
  C_index s a b 0 0 (C_zero s a b) (C_zero s a b)

theorem tower_lt_first (s : Supply) (n : Nat) : tower s n < I s 0 0 := by
  cases n with
  | zero => exact regular_pos (first_regular s)
  | succ n => exact psi_lt s _ _ (first_regular s)

theorem tower_lt_succ (s : Supply) (n : Nat) : tower s n < tower s (n + 1) := by
  induction n with
  | zero => exact psi_pos s _ _ (regular_pos (first_regular s))
  | succ n ih =>
    exact psi_strict_of_mem s _ _ _ (Or.inl ⟨0, rfl⟩) ih
      (first_mem_C s _ _) (C_seed s _ _ _ ih)

theorem tower_strict (s : Supply) {n m : Nat} (h : n < m) : tower s n < tower s m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hl | rfl
    · exact lt_trans _ _ _ (ih hl) (tower_lt_succ s m)
    · exact tower_lt_succ s n

theorem tower_mono (s : Supply) {n m : Nat} (h : n ≤ m) : tower s n ≤ tower s m := by
  rcases Nat.lt_or_eq_of_le h with hl | rfl
  · exact Or.inl (tower_strict s hl)
  · exact le_refl _

theorem tower_lt_sup (s : Supply) (n : Nat) : tower s n < sup (tower s) :=
  lt_of_lt_of_le (tower_lt_succ s n) (le_sup (tower s) (n + 1))

theorem tower_sup_lt_first (s : Supply) : sup (tower s) < I s 0 0 := by
  obtain ⟨b, hb, hbound⟩ := small_nat (first_regular s) (tower s) (tower_lt_first s)
  exact lt_of_le_of_lt ((sup_le_iff _ b).mpr (fun n => Or.inl (hbound n))) hb

theorem tower_sup_add_closed (s : Supply) {x y : O}
    (hx : x < sup (tower s)) (hy : y < sup (tower s)) : x + y < sup (tower s) := by
  obtain ⟨n, hn⟩ := (lt_sup_iff _ x).mp hx
  obtain ⟨m, hm⟩ := (lt_sup_iff _ y).mp hy
  have hx' := lt_of_lt_of_le hn (tower_mono s (Nat.le_max_left n m))
  have hy' := lt_of_lt_of_le hm (tower_mono s (Nat.le_max_right n m))
  have hadd := (psi_addPrincipal s (I s 0 0) (tower s (max n m)) (first_regular s))
    x y (lt_trans _ _ _ hx' (tower_lt_succ s _))
      (lt_trans _ _ _ hy' (tower_lt_succ s _))
  exact lt_trans _ _ _ hadd (tower_lt_sup s (max n m + 1))

theorem index_eq_first_of_psi_lt_first (s : Supply) (k a : O)
    (hk : RegularIndex s k) (h : psi s k a < I s 0 0) : k = I s 0 0 := by
  rcases regularIndex_lower_bound s k hk with hl | he
  · exact False.elim (lt_asymm h (psi_closed s k a _ (first_mem_C s _ _) hl))
  · exact he.symm

theorem C_first_tower_sup (s : Supply) (x : O)
    (hx : C s (I s 0 0) (sup (tower s)) x) (hbound : x < I s 0 0) :
    x < sup (tower s) := by
  have h := (C_iff s _ _ x).mp hx
  clear hx
  induction h with
  | zero => exact tower_lt_sup s 0
  | seed hx => exact hx
  | @add x y hx hy ihx ihy =>
    exact tower_sup_add_closed s (ihx (lt_of_le_of_lt (le_add x y) hbound))
      (ihy (lt_of_le_of_lt (right_le_add x y) hbound))
  | @index x y hx hy ihx ihy =>
    exact False.elim (((not_lt_iff_le _ _).mpr (I_lower_bound s x y)) hbound)
  | @collapse k b hb hk hc hd ihc ihd =>
    change psi s k b < sup (tower s)
    rw [index_eq_first_of_psi_lt_first s k b hk hbound]
    obtain ⟨n, hn⟩ := (lt_sup_iff _ b).mp (ihd hb)
    exact lt_of_le_of_lt (psi_mono s _ b (tower s n) (Or.inl hn))
      (tower_lt_sup s (n + 1))

/-- The tower is cofinal in the actual collapse, not a newly named supremum. -/
theorem tower_sup_eq_psi_first_first (s : Supply) :
    sup (tower s) = psi s (I s 0 0) (I s 0 0) := by
  apply le_antisymm
  · apply (sup_le_iff _ _).mpr
    intro n
    cases n with
    | zero => exact zero_le _
    | succ n => exact psi_mono s _ _ _ (Or.inl (tower_lt_first s n))
  · exact psi_min s _ _ _ ⟨Or.inl (tower_sup_lt_first s), C_first_tower_sup s⟩

theorem tower_fundamentalSequence (s : Supply) (offset : Nat) :
    FundamentalSequence (psi s (I s 0 0) (I s 0 0))
      (fun n => tower s (n + offset)) := by
  rw [← tower_sup_eq_psi_first_first]
  refine ⟨fun n => tower_lt_sup s _, fun n m h => tower_strict s (by omega), ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := (lt_sup_iff _ x).mp hx
  exact ⟨n, lt_of_lt_of_le hn (tower_mono s (by omega))⟩

/-- Normal-form argument condition for every tower stage. -/
theorem tower_argument_normal (s : Supply) (n : Nat) :
    C s (tower s n) (psi s (I s 0 0) (tower s n)) (tower s n) :=
  C_seed s _ _ _ (tower_lt_succ s n)

theorem first_diagonal_argument_normal (s : Supply) :
    C s (I s 0 0) (psi s (I s 0 0) (I s 0 0)) (I s 0 0) := first_mem_C s _ _

end
end OCF.Denis
