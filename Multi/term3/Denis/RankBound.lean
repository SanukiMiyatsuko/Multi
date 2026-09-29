import Multi.term3.Denis.IndexIteration

/-! Bounds for finite normal notations. These bounds discharge the rank
support premise in the successor-rank zero-argument sequence rule. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def rankTower (s : Supply) : Nat → O
  | 0 => 0
  | n + 1 => I s (rankTower s n) 0

theorem first_rank_mono (s : Supply) {r q : O} (h : r ≤ q) : first s r ≤ first s q := by
  rcases h with h | rfl
  · exact Or.inl (first_rank_strict s h)
  · exact le_refl _

theorem rankTower_lt_succ (s : Supply) (n : Nat) : rankTower s n < rankTower s (n + 1) := by
  induction n with
  | zero => exact regular_pos (inaccessible_regular (first_inaccessible s 0))
  | succ n ih =>
    change I s (rankTower s n) 0 < I s (rankTower s (n + 1)) 0
    rw [I_zero, I_zero]
    exact first_rank_strict s ih

theorem rankTower_mono (s : Supply) {n m : Nat} (h : n ≤ m) : rankTower s n ≤ rankTower s m := by
  induction h with
  | refl => exact le_refl _
  | @step m h ih => exact le_trans ih (Or.inl (rankTower_lt_succ s m))

def RankBounded (s : Supply) (x : O) : Prop := ∃ n, x < rankTower s n

theorem rankBounded_zero (s : Supply) : RankBounded s 0 := ⟨1, rankTower_lt_succ s 0⟩

theorem rankBounded_down (s : Supply) {x y : O} (h : x ≤ y) (hy : RankBounded s y) :
    RankBounded s x := by
  obtain ⟨n, hn⟩ := hy
  exact ⟨n, lt_of_le_of_lt h hn⟩

theorem rankBounded_add (s : Supply) {x y : O} (hx : RankBounded s x) (hy : RankBounded s y) :
    RankBounded s (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  have hx' := lt_of_lt_of_le hn (rankTower_mono s (Nat.le_max_left n m))
  have hy' := lt_of_lt_of_le hm (rankTower_mono s (Nat.le_max_right n m))
  exact ⟨max n m + 1, regular_add_closed
    (inaccessible_regular (first_inaccessible s (rankTower s (max n m))))
    (lt_trans _ _ _ hx' (rankTower_lt_succ s _))
    (lt_trans _ _ _ hy' (rankTower_lt_succ s _))⟩

theorem rankBounded_I (s : Supply) {r b : O} (hr : RankBounded s r) (hb : RankBounded s b) :
    RankBounded s (I s r b) := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hb
  have hr' := lt_of_lt_of_le hn (rankTower_mono s (Nat.le_max_left n m))
  have hb' := lt_of_lt_of_le hm (rankTower_mono s (Nat.le_max_right n m))
  exact ⟨max n m + 1,
    I_lt_inaccessible s (first_inaccessible s (rankTower s (max n m))) r b hr'
      (lt_trans _ _ _ hb' (rankTower_lt_succ s _))⟩

theorem rank_lt_first_of_bounded (s : Supply) (r : O) (hr : RankBounded s r) : r < first s r := by
  rcases lt_total r (first s r) with h | h | h
  · exact h
  all_goals
    have hfr : first s r ≤ r := by first | exact Or.inr h.symm | exact Or.inl h
    have ht : ∀ n, rankTower s n ≤ r := by
      intro n
      induction n with
      | zero => exact zero_le _
      | succ n ih =>
        change I s (rankTower s n) 0 ≤ r
        rw [I_zero]
        exact le_trans (first_rank_mono s ih) hfr
    obtain ⟨n, hn⟩ := hr
    exact False.elim (lt_irrefl _ (lt_of_lt_of_le hn (ht n)))

theorem rank_lt_psi_first_succ_rank (s : Supply) (r : O) (hr : RankBounded s r) :
    r < psi s (I s (succ r) 0) 0 := by
  let p := psi s (I s (succ r) 0) 0
  have hk := first_inaccessible s (succ r)
  have hp := psi_lt s _ 0 (inaccessible_regular hk)
  rcases lt_total r p with h | h | h
  · exact h
  all_goals
    have hpr : p ≤ r := by first | exact Or.inr h.symm | exact Or.inl h
    have ht : ∀ n, rankTower s n < p := by
      intro n
      induction n with
      | zero => exact psi_pos s _ _ (regular_pos (inaccessible_regular hk))
      | succ n ih =>
        have hi : rankTower s n < succ r :=
          lt_of_lt_of_le ih (le_trans hpr (Or.inl (lt_succ_self r)))
        have hz : 0 < p := psi_pos s _ _ (regular_pos (inaccessible_regular hk))
        exact psi_closed s _ _ _
          (C_index s 0 p _ 0 (C_seed s 0 p _ ih) (C_zero s 0 p))
          (I_lt_inaccessible s hk _ 0 hi (regular_pos (inaccessible_regular hk)))
    obtain ⟨n, hn⟩ := hr
    exact False.elim (lt_irrefl _ (lt_of_lt_of_le (lt_trans _ _ _ hn (ht n)) hpr))

theorem bounded_rank_zero_fundamentalSequence (s : Supply) (r : O) (hr : RankBounded s r) :
    FundamentalSequence (psi s (I s (succ r) 0) 0) (indexIter s r) :=
  first_succ_rank_zero_fundamentalSequence s r
    (C_seed s _ _ _ (rank_lt_psi_first_succ_rank s r hr))

end
end OCF.Denis
