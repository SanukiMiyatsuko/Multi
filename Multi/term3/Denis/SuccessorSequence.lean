import Multi.term3.Denis.RevisedDomains

/-! The successor-argument branch at the first regular index, derived from
the actual closure. The predecessor argument's admissibility is explicit.
No global strictness of psi is assumed. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def repeatAdd (b : O) : Nat → O
  | 0 => 0
  | n + 1 => b + repeatAdd b n

theorem repeatAdd_add (b : O) (n m : Nat) :
    repeatAdd b n + repeatAdd b m = repeatAdd b (n + m) := by
  induction n with
  | zero => simp only [repeatAdd, Nat.zero_add, zero_add]
  | succ n ih =>
    change (b + repeatAdd b n) + repeatAdd b m = _
    rw [add_assoc, ih]
    exact congrArg (repeatAdd b) (Nat.succ_add n m).symm

theorem repeatAdd_lt_succ (b : O) (hb : 0 < b) (n : Nat) :
    repeatAdd b n < repeatAdd b (n + 1) := by
  induction n with
  | zero => simpa [repeatAdd, add_zero] using hb
  | succ n ih => exact add_lt_add_right b ih

theorem repeatAdd_strict (b : O) (hb : 0 < b) {n m : Nat} (h : n < m) :
    repeatAdd b n < repeatAdd b m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hl | rfl
    · exact lt_trans _ _ _ (ih hl) (repeatAdd_lt_succ b hb m)
    · exact repeatAdd_lt_succ b hb n

theorem repeatAdd_lt_sup (b : O) (hb : 0 < b) (n : Nat) :
    repeatAdd b n < sup (repeatAdd b) :=
  lt_of_lt_of_le (repeatAdd_lt_succ b hb n) (le_sup _ (n + 1))

theorem repeatAdd_sup_addPrincipal (b : O) : AddPrincipal (sup (repeatAdd b)) := by
  intro x y hx hy
  obtain ⟨n, hn⟩ := (lt_sup_iff _ x).mp hx
  obtain ⟨m, hm⟩ := (lt_sup_iff _ y).mp hy
  have h := lt_of_le_of_lt (add_mono_left (Or.inl hn) y) (add_lt_add_right (repeatAdd b n) hm)
  rw [repeatAdd_add] at h
  exact lt_of_lt_of_le h (le_sup _ (n + m))

theorem repeatAdd_lt_regular (b k : O) (hk : UncountableRegular k) (hb : b < k) (n : Nat) :
    repeatAdd b n < k := by
  induction n with
  | zero => exact regular_pos hk
  | succ n ih => exact regular_add_closed hk hb ih

theorem repeatAdd_sup_lt_regular (b k : O) (hk : UncountableRegular k) (hb : b < k) :
    sup (repeatAdd b) < k := by
  obtain ⟨c, hc, hfc⟩ := small_nat hk (repeatAdd b) (repeatAdd_lt_regular b k hk hb)
  exact lt_of_le_of_lt ((sup_le_iff _ c).mpr (fun n => Or.inl (hfc n))) hc

theorem C_first_successor_repeat (s : Supply) (a x : O)
    (hx : C s (succ a) (sup (repeatAdd (psi s (I s 0 0) a))) x)
    (hbound : x < I s 0 0) : x < sup (repeatAdd (psi s (I s 0 0) a)) := by
  have h := (C_iff s _ _ x).mp hx
  have hpos := psi_pos s (I s 0 0) a (regular_pos (first_regular s))
  clear hx
  induction h with
  | zero => exact repeatAdd_lt_sup _ hpos 0
  | seed hx => exact hx
  | @add x y hx hy ihx ihy =>
    exact repeatAdd_sup_addPrincipal _ x y
      (ihx (lt_of_le_of_lt (le_add x y) hbound))
      (ihy (lt_of_le_of_lt (right_le_add x y) hbound))
  | @index x y hx hy ihx ihy =>
    exact False.elim (((not_lt_iff_le _ _).mpr (I_lower_bound s x y)) hbound)
  | @collapse k b hb hk hc hd ihc ihd =>
    change psi s k b < _
    rw [index_eq_first_of_psi_lt_first s k b hk hbound]
    have hba := psi_mono s (I s 0 0) b a ((lt_succ_iff_le b a).mp hb)
    have hlast := repeatAdd_lt_sup (psi s (I s 0 0) a) hpos 1
    simp only [repeatAdd, add_zero] at hlast
    exact lt_of_le_of_lt hba hlast

theorem psi_first_successor_eq_repeat_sup (s : Supply) (a : O)
    (ha : C s a (psi s (I s 0 0) a) a) :
    psi s (I s 0 0) (succ a) = sup (repeatAdd (psi s (I s 0 0) a)) := by
  let k := I s 0 0
  let b := psi s k a
  let parent := psi s k (succ a)
  have hb : b < k := psi_lt s k a (first_regular s)
  apply le_antisymm
  · exact psi_min s k (succ a) _
      ⟨Or.inl (repeatAdd_sup_lt_regular b k (first_regular s) hb), C_first_successor_repeat s a⟩
  · have ha' : C s (succ a) parent a :=
      C_mono_seed s (succ a) b parent (psi_mono s k a (succ a) (Or.inl (lt_succ_self a))) a
        (C_mono_argument s a (succ a) b (Or.inl (lt_succ_self a)) a ha)
    have hbC : C s (succ a) parent b := C_collapse s (succ a) parent k a
      (lt_succ_self a) (Or.inl ⟨0, rfl⟩) (first_mem_C s _ _) ha'
    have hfn : ∀ n, C s (succ a) parent (repeatAdd b n) := by
      intro n
      induction n with
      | zero => exact C_zero s _ _
      | succ n ih => exact C_add s _ _ _ _ hbC ih
    exact (sup_le_iff _ parent).mpr (fun n => Or.inl
      (psi_closed s k (succ a) _ (hfn n) (repeatAdd_lt_regular b k (first_regular s) hb n)))

theorem psi_first_successor_fundamentalSequence (s : Supply) (a : O)
    (ha : C s a (psi s (I s 0 0) a) a) :
    FundamentalSequence (psi s (I s 0 0) (succ a)) (repeatAdd (psi s (I s 0 0) a)) := by
  rw [psi_first_successor_eq_repeat_sup s a ha]
  have hb := psi_pos s (I s 0 0) a (regular_pos (first_regular s))
  exact ⟨repeatAdd_lt_sup _ hb, fun _ _ h => repeatAdd_strict _ hb h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

/-- If a below the collapse index has already fallen outside the seed,
allowing the argument a adds nothing to the closure. -/
theorem C_successor_plateau (s : Supply) (k a : O) (hak : a < k)
    (hpa : psi s k a ≤ a) (x : O) (hx : C s (succ a) (psi s k a) x) :
    C s a (psi s k a) x := by
  apply C_least s (succ a) (psi s k a) (C s a (psi s k a)) _ _ _ _ _ x hx
  · exact C_zero s _ _
  · exact fun x hx => C_seed s _ _ x hx
  · exact fun x y hx hy => C_add s _ _ x y hx hy
  · exact fun x y hx hy => C_index s _ _ x y hx hy
  · intro j b hb hj hc hd
    rcases (lt_succ_iff_le b a).mp hb with hb | heq
    · exact C_collapse s _ _ j b hb hj hc hd
    · rw [heq] at hd
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le (psi_closed s k a a hd hak) hpa))

theorem psi_successor_plateau (s : Supply) (k a : O) (hak : a < k)
    (hpa : psi s k a ≤ a) : psi s k (succ a) = psi s k a := by
  apply le_antisymm _ (psi_mono s k a (succ a) (Or.inl (lt_succ_self a)))
  exact psi_min s k (succ a) (psi s k a) ⟨psi_le s k a,
    fun x hx hxk => psi_closed s k a x (C_successor_plateau s k a hak hpa x hx) hxk⟩

/-- Once a countable argument lies beyond its collapse, every argument
below the same index has collapse at most that value. -/
theorem psi_bounded_of_postfixed (s : Supply) (k a c : O)
    (hc : c < k) (hpa : psi s k a ≤ a) : psi s k c ≤ psi s k a := by
  have lift (x : O) (hx : C s c (psi s k a) x) : C s a (psi s k a) x := by
    apply C_least s c (psi s k a) (C s a (psi s k a)) _ _ _ _ _ x hx
    · exact C_zero s _ _
    · exact fun x hx => C_seed s _ _ x hx
    · exact fun x y hx hy => C_add s _ _ x y hx hy
    · exact fun x y hx hy => C_index s _ _ x y hx hy
    · intro j b hb hj hk harg
      have hba := lt_of_lt_of_le (psi_closed s k a b harg (lt_trans _ _ _ hb hc)) hpa
      exact C_collapse s a _ j b hba hj hk harg
  exact psi_min s k c (psi s k a) ⟨psi_le s k a,
    fun x hx hxk => psi_closed s k a x (lift x hx) hxk⟩

theorem psi_argument_normal_below (s : Supply) (k a b : O) (hak : a < k)
    (ha : C s a (psi s k a) a) (hba : b < a) : b < psi s k b := by
  have hap := psi_closed s k a a ha hak
  rcases lt_total b (psi s k b) with h | h | h
  · exact h
  · have hbound := psi_bounded_of_postfixed s k b a hak (Or.inr h.symm)
    rw [← h] at hbound
    exact False.elim (lt_irrefl _ (lt_trans _ _ _ (lt_of_lt_of_le hap hbound) hba))
  · have hbound := psi_bounded_of_postfixed s k b a hak (Or.inl h)
    exact False.elim (lt_irrefl _
      (lt_trans _ _ _ (lt_of_lt_of_le hap hbound) (lt_trans _ _ _ h hba)))

/-- A normal successor argument below the regular index forces its
predecessor to be admissible at the predecessor collapse. -/
theorem psi_predecessor_argument_normal (s : Supply) (k a : O)
    (hk : UncountableRegular k) (hak : a < k)
    (ha : C s (succ a) (psi s k (succ a)) (succ a)) : C s a (psi s k a) a := by
  classical
  have hnext := psi_closed s k (succ a) (succ a) ha (regular_succ_lt hk hak)
  have hprev : a < psi s k a := by
    rcases lt_total a (psi s k a) with h | h | h
    · exact h
    · rw [psi_successor_plateau s k a hak (Or.inr h.symm)] at hnext
      rw [← h] at hnext
      exact False.elim (lt_asymm (lt_succ_self a) hnext)
    · rw [psi_successor_plateau s k a hak (Or.inl h)] at hnext
      exact False.elim (lt_irrefl _ (lt_trans _ _ _ (lt_succ_self a) (lt_trans _ _ _ hnext h)))
  exact C_seed s a _ a hprev

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem repeatAdd_represented (s : OCF.Denis.Supply) (b : OCF.Denis.O)
    (hb : Represented s b) (n : Nat) : Represented s (OCF.Denis.repeatAdd b n) := by
  induction n with
  | zero => exact ⟨.zero, .zero, rfl⟩
  | succ n ih => exact represented_add s b _ hb ih

theorem psi_first_successor_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s a) (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) a) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a)) := by
  have hb : Represented s (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) :=
    represented_psi_of_mem s _ a ⟨omega1, omega1_isNormal s, rfl⟩ ha (Or.inl ⟨0, rfl⟩) harg
  exact dense_of_normal_sequence s _ _ (OCF.Denis.psi_first_successor_fundamentalSequence s a harg)
    (repeatAdd_represented s _ hb)

theorem revised_psi_first_successor_fundamentalSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s a) (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) a) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (psi_first_successor_dense s a ha harg)

/-- For normal countable successor arguments the extra predecessor
membership premise is derived from the parent's normality condition. -/
theorem revised_psi_first_normal_successor_fundamentalSequence (s : OCF.Denis.Supply)
    (a : OCF.Denis.O) (ha : Represented s (succ a)) (hak : a < OCF.Denis.I s 0 0)
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a)) (succ a)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))) :=
  revised_psi_first_successor_fundamentalSequence s a (represented_predecessor s a ha)
    (OCF.Denis.psi_predecessor_argument_normal s _ a (OCF.Denis.first_regular s) hak harg)

end
end T.Correspondence.Denis.Covering
