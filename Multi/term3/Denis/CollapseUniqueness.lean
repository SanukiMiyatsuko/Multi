import Multi.term3.Denis.IndexTrees

/-! A uniqueness lemma for collapse presentations whose index and argument
are both in their defining closure. The current raw IsNormal predicate
only requires the argument condition; this lemma does not silently add
the missing index premise to every normal term. -/

namespace OCF.Denis
open Ordinal

theorem psi_mono_index (s : Supply) (k l a : O) (hkl : k ≤ l) : psi s k a ≤ psi s l a := by
  rcases lt_total (psi s l a) k with h | h | h
  · apply psi_min s k a (psi s l a)
    exact ⟨Or.inl h, fun x hx hxk => psi_closed s l a x hx (lt_of_lt_of_le hxk hkl)⟩
  · exact le_trans (psi_le s k a) (Or.inr h.symm)
  · exact le_trans (psi_le s k a) (Or.inl h)

theorem psi_mono_both (s : Supply) (k l a b : O) (hkl : k ≤ l) (hab : a ≤ b) :
    psi s k a ≤ psi s l b :=
  le_trans (psi_mono_index s k l a hkl) (psi_mono s l a b hab)

/-- The collapse is constant on every index interval from its value up
to its original index. This includes non-regular boundary indices of
the total ordinal definition. -/
theorem psi_index_plateau (s : Supply) (k l a : O)
    (hlower : psi s l a ≤ k) (hupper : k ≤ l) : psi s k a = psi s l a := by
  have hmono := psi_mono_index s k l a hupper
  apply le_antisymm hmono
  apply psi_min s l a (psi s k a)
  refine ⟨le_trans (psi_le s k a) hupper, ?_⟩
  intro x hx hxl
  have hxC := C_mono_seed s a (psi s k a) (psi s l a) hmono x hx
  have hxlower := psi_closed s l a x hxC hxl
  exact psi_closed s k a x hx (lt_of_lt_of_le hxlower hlower)

theorem psi_index_idempotent (s : Supply) (k a : O) : psi s (psi s k a) a = psi s k a :=
  psi_index_plateau s _ k a (le_refl _) (psi_le s k a)

/-- A collapse already present above the seed must have an earlier
argument, even if it has a second syntactic presentation. -/
theorem C_collapse_argument_lt (s : Supply) (cutoff beta k a : O)
    (hk : RegularIndex s k) (hb : beta ≤ psi s k a)
    (hx : C s cutoff beta (psi s k a)) : a < cutoff := by
  have impossible (h : cutoff ≤ a) : False := by
    have hx' := C_mono_seed s a beta (psi s k a) hb (psi s k a)
      (C_mono_argument s cutoff a beta h (psi s k a) hx)
    exact lt_irrefl _ (psi_closed s k a _ hx' (psi_lt s k a (regularIndex_regular s k hk)))
  rcases lt_total a cutoff with h | h | h
  · exact h
  · exact False.elim (impossible (Or.inr h.symm))
  · exact False.elim (impossible (Or.inl h))

theorem psi_ne_of_argument_lt (s : Supply) (k a l b : O)
    (hk : RegularIndex s k) (hl : RegularIndex s l) (hab : a < b)
    (hkC : C s a (psi s k a) k) (haC : C s a (psi s k a) a) :
    psi s k a ≠ psi s l b := by
  intro heq
  have hkC' := C_mono_argument s a b (psi s k a) (Or.inl hab) k hkC
  have haC' := C_mono_argument s a b (psi s k a) (Or.inl hab) a haC
  have hval := C_collapse s b (psi s k a) k a hab hk hkC' haC'
  rw [heq] at hval
  exact lt_irrefl _ (psi_closed s l b _ hval (psi_lt s l b (regularIndex_regular s l hl)))

theorem psi_normal_parameters_unique (s : Supply) (k a l b : O)
    (hk : RegularIndex s k) (hl : RegularIndex s l)
    (hkC : C s a (psi s k a) k) (haC : C s a (psi s k a) a)
    (hlC : C s b (psi s l b) l) (hbC : C s b (psi s l b) b)
    (heq : psi s k a = psi s l b) : k = l ∧ a = b := by
  have hab : a = b := by
    rcases lt_total a b with h | h | h
    · exact False.elim (psi_ne_of_argument_lt s k a l b hk hl h hkC haC heq)
    · exact h
    · exact False.elim (psi_ne_of_argument_lt s l b k a hl hk h hlC hbC heq.symm)
  subst b
  refine ⟨?_, rfl⟩
  rcases lt_total k l with h | h | h
  · rw [heq] at hkC
    have hkl := psi_closed s l a k hkC h
    have hval := psi_lt s k a (regularIndex_regular s k hk)
    rw [heq] at hval
    exact False.elim (lt_asymm hkl hval)
  · exact h
  · rw [← heq] at hlC
    have hlk := psi_closed s k a l hlC h
    have hval := psi_lt s l a (regularIndex_regular s l hl)
    rw [← heq] at hval
    exact False.elim (lt_asymm hlk hval)

end OCF.Denis
