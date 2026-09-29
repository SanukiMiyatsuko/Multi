import Multi.term3.Denis.IndexLaws

/-! The iteration clause for collapse of the first successor-rank index.
The rank-support premise is explicit; for rank zero it is discharged by
the zero constructor of the closure. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def indexIter (s : Supply) (r : O) : Nat → O
  | 0 => 0
  | n + 1 => I s r (indexIter s r n)

theorem indexIter_lt_succ (s : Supply) (r : O) (n : Nat) :
    indexIter s r n < indexIter s r (n + 1) := by
  induction n with
  | zero => exact regular_pos (regularIndex_regular s _ (Or.inl ⟨r, rfl⟩))
  | succ n ih => exact I_strict s r ih

theorem indexIter_strict (s : Supply) (r : O) {n m : Nat} (h : n < m) :
    indexIter s r n < indexIter s r m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hl | rfl
    · exact lt_trans _ _ _ (ih hl) (indexIter_lt_succ s r m)
    · exact indexIter_lt_succ s r n

theorem indexIter_mono (s : Supply) (r : O) {n m : Nat} (h : n ≤ m) :
    indexIter s r n ≤ indexIter s r m := by
  rcases Nat.lt_or_eq_of_le h with hl | rfl
  · exact Or.inl (indexIter_strict s r hl)
  · exact le_refl _

theorem first_inaccessible (s : Supply) (r : O) : Inaccessible r (I s r 0) := by
  rw [I_zero]
  exact first_spec s r

theorem indexIter_lt_first_succ_rank (s : Supply) (r : O) (n : Nat) :
    indexIter s r n < I s (succ r) 0 := by
  induction n with
  | zero => exact regular_pos (inaccessible_regular (first_inaccessible s (succ r)))
  | succ n ih => exact I_lt_inaccessible s (first_inaccessible s (succ r)) r _ (lt_succ_self r) ih

theorem indexIter_lt_sup (s : Supply) (r : O) (n : Nat) :
    indexIter s r n < sup (indexIter s r) :=
  lt_of_lt_of_le (indexIter_lt_succ s r n) (le_sup (indexIter s r) (n + 1))

theorem indexIter_sup_fixedpoint (s : Supply) (r : O) :
    I s r (sup (indexIter s r)) = sup (indexIter s r) := by
  have hf : FundamentalSequence (sup (indexIter s r)) (indexIter s r) :=
    ⟨indexIter_lt_sup s r, fun _ _ h => indexIter_strict s r h,
      fun x hx => (lt_sup_iff _ x).mp hx⟩
  have hleft := I_fundamentalSequence s r _ _ hf
  have hright := hf.shift 1
  exact hleft.sup_eq.symm.trans hright.sup_eq

theorem indexIter_sup_lt_first_succ_rank (s : Supply) (r : O) :
    sup (indexIter s r) < I s (succ r) 0 := by
  obtain ⟨b, hb, hbound⟩ := small_nat
    (inaccessible_regular (first_inaccessible s (succ r)))
    (indexIter s r) (indexIter_lt_first_succ_rank s r)
  exact lt_of_le_of_lt ((sup_le_iff _ b).mpr (fun n => Or.inl (hbound n))) hb

theorem indexIter_sup_add_closed (s : Supply) (r : O) {x y : O}
    (hx : x < sup (indexIter s r)) (hy : y < sup (indexIter s r)) :
    x + y < sup (indexIter s r) := by
  obtain ⟨n, hn⟩ := (lt_sup_iff _ x).mp hx
  obtain ⟨m, hm⟩ := (lt_sup_iff _ y).mp hy
  have hx' := lt_of_lt_of_le hn (indexIter_mono s r (Nat.le_max_left n m))
  have hy' := lt_of_lt_of_le hm (indexIter_mono s r (Nat.le_max_right n m))
  have hadd := I_addPrincipal s r (indexIter s r (max n m)) x y
    (lt_trans _ _ _ hx' (indexIter_lt_succ s r _))
    (lt_trans _ _ _ hy' (indexIter_lt_succ s r _))
  exact lt_trans _ _ _ hadd (indexIter_lt_sup s r (max n m + 1))

theorem rank_le_of_I_lt_first_succ_rank (s : Supply) (q b r : O)
    (h : I s q b < I s (succ r) 0) : q ≤ r := by
  apply (not_lt_iff_le _ _).mp
  intro hrq
  have hsq := (succ_le_iff_lt r q).mpr hrq
  have hh : first s (succ r) ≤ first s q := by
    rcases hsq with hh | hh
    · exact Or.inl (first_rank_strict s hh)
    · exact Or.inr (congrArg (first s) hh)
  have hq := I_mono s q (zero_le b)
  rw [I_zero] at hq
  rw [I_zero s (succ r)] at h
  exact lt_irrefl _ (lt_of_lt_of_le h (le_trans hh hq))

theorem C_zero_indexIter_sup (s : Supply) (r x : O)
    (hx : C s 0 (sup (indexIter s r)) x) (hbound : x < I s (succ r) 0) :
    x < sup (indexIter s r) := by
  have h := (C_iff s _ _ x).mp hx
  clear hx
  induction h with
  | zero => exact indexIter_lt_sup s r 0
  | seed hx => exact hx
  | @add x y hx hy ihx ihy =>
    exact indexIter_sup_add_closed s r (ihx (lt_of_le_of_lt (le_add x y) hbound))
      (ihy (lt_of_le_of_lt (right_le_add x y) hbound))
  | @index q b hq hb ihq ihb =>
    have hqr := rank_le_of_I_lt_first_succ_rank s q b r hbound
    have hb' := ihb (lt_of_le_of_lt (index_le_I s q b) hbound)
    obtain ⟨n, hn⟩ := (lt_sup_iff _ b).mp hb'
    rcases hqr with hqr | rfl
    · have hbI : b < I s r (indexIter s r n) :=
        lt_trans _ _ _ hn (indexIter_lt_succ s r n)
      exact lt_trans _ _ _ (I_lower_rank_closed s q r _ b hqr hbI)
        (indexIter_lt_sup s r (n + 1))
    · exact lt_trans _ _ _ (I_strict s q hn) (indexIter_lt_sup s q (n + 1))
  | collapse hb _ _ _ _ _ => exact False.elim (not_lt_zero _ hb)

theorem indexIter_sup_eq_psi_first_succ_rank (s : Supply) (r : O)
    (hr : C s 0 (psi s (I s (succ r) 0) 0) r) :
    sup (indexIter s r) = psi s (I s (succ r) 0) 0 := by
  apply le_antisymm
  · have hc : ∀ n, C s 0 (psi s (I s (succ r) 0) 0) (indexIter s r n) := by
      intro n
      induction n with
      | zero => exact C_zero s _ _
      | succ n ih => exact C_index s _ _ r _ hr ih
    exact (sup_le_iff _ _).mpr (fun n => Or.inl
      (psi_closed s _ _ _ (hc n) (indexIter_lt_first_succ_rank s r n)))
  · exact psi_min s _ _ _
      ⟨Or.inl (indexIter_sup_lt_first_succ_rank s r), C_zero_indexIter_sup s r⟩

theorem first_succ_rank_zero_fundamentalSequence (s : Supply) (r : O)
    (hr : C s 0 (psi s (I s (succ r) 0) 0) r) :
    FundamentalSequence (psi s (I s (succ r) 0) 0) (indexIter s r) := by
  rw [← indexIter_sup_eq_psi_first_succ_rank s r hr]
  exact ⟨indexIter_lt_sup s r, fun _ _ h => indexIter_strict s r h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

theorem first_inaccessible_zero_fundamentalSequence (s : Supply) :
    FundamentalSequence (psi s (I s (succ 0) 0) 0) (indexIter s 0) :=
  first_succ_rank_zero_fundamentalSequence s 0 (C_zero s _ _)

end
end OCF.Denis
