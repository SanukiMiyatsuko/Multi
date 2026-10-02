import Multi.term3.Denis.CompletenessReduction

/-! Continuity of every collapse in its argument at limits, and the
argument condition at each successor jump.

A closure derivation uses finitely many seeds and collapse arguments, so
`psi k e` for a limit `e` is the supremum of the earlier values. Hence the
least argument whose collapse exceeds a given value is zero or a successor
`succ e'`, and at such a jump `e'` belongs to its own defining closure. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem stage_mono (s : Supply) (k c d x : O) (hcd : c ≤ d)
    (hx : C s c (psi s k c) x) : C s d (psi s k d) x :=
  C_mono_seed s d _ _ (psi_mono s k c d hcd) x (C_mono_argument s c d _ hcd x hx)

theorem stage_pair (s : Supply) (k e x y : O)
    (hx : ∃ e', e' < e ∧ C s e' (psi s k e') x) (hy : ∃ e', e' < e ∧ C s e' (psi s k e') y) :
    ∃ e', e' < e ∧ C s e' (psi s k e') x ∧ C s e' (psi s k e') y := by
  obtain ⟨e1, he1, hx1⟩ := hx
  obtain ⟨e2, he2, hy2⟩ := hy
  rcases lt_total e1 e2 with h | h | h
  · exact ⟨e2, he2, stage_mono s k e1 e2 x (Or.inl h) hx1, hy2⟩
  · subst h
    exact ⟨e1, he1, hx1, hy2⟩
  · exact ⟨e1, he1, hx1, stage_mono s k e2 e1 y (Or.inl h) hy2⟩

/-- Closure elements at a limit cutoff, with seeds below the supremum of
earlier collapse values, already occur at an earlier stage. -/
theorem C_limit_stage (s : Supply) (k e sigma : O) (he : IsLimit e)
    (hsig : ∀ x, x < sigma → ∃ e', e' < e ∧ x < psi s k e')
    (x : O) (hx : C s e sigma x) : ∃ e', e' < e ∧ C s e' (psi s k e') x := by
  have hpos : 0 < e := (zero_lt_iff_ne_zero e).mpr he.1
  apply C_least s e sigma (fun x => ∃ e', e' < e ∧ C s e' (psi s k e') x) _ _ _ _ _ x hx
  · exact ⟨0, hpos, C_zero s 0 _⟩
  · intro x hx
    obtain ⟨e', he', hlt⟩ := hsig x hx
    exact ⟨e', he', C_seed s e' _ x hlt⟩
  · intro x y hx hy
    obtain ⟨e', he', hx', hy'⟩ := stage_pair s k e x y hx hy
    exact ⟨e', he', C_add s e' _ x y hx' hy'⟩
  · intro x y hx hy
    obtain ⟨e', he', hx', hy'⟩ := stage_pair s k e x y hx hy
    exact ⟨e', he', C_index s e' _ x y hx' hy'⟩
  · intro l f hf hl hlP hfP
    have hsf : ∃ e', e' < e ∧ C s e' (psi s k e') 0 :=
      ⟨succ f, succ_lt_limit he hf, C_zero s _ _⟩
    obtain ⟨e1, he1, hl1, hf1⟩ := stage_pair s k e l f hlP hfP
    obtain ⟨e2, he2, hl2, _⟩ := stage_pair s k e l 0 ⟨e1, he1, hl1⟩ hsf
    have hmax : ∃ e', e' < e ∧ f < e' ∧ C s e' (psi s k e') l ∧ C s e' (psi s k e') f := by
      rcases lt_total f e1 with h | h | h
      · exact ⟨e1, he1, h, hl1, hf1⟩
      · refine ⟨succ e1, succ_lt_limit he he1, h ▸ lt_succ_self e1,
          stage_mono s k e1 _ l (Or.inl (lt_succ_self e1)) hl1,
          stage_mono s k e1 _ f (Or.inl (lt_succ_self e1)) hf1⟩
      · refine ⟨succ f, succ_lt_limit he hf, lt_succ_self f,
          stage_mono s k e1 _ l (Or.inl (lt_trans _ _ _ h (lt_succ_self f))) hl1,
          stage_mono s k e1 _ f (Or.inl (lt_trans _ _ _ h (lt_succ_self f))) hf1⟩
    obtain ⟨e3, he3, hfe3, hl3, hf3⟩ := hmax
    exact ⟨e3, he3, C_collapse s e3 _ l f hfe3 hl hl3 hf3⟩

/-- Continuity at limits: a bound for all earlier collapse values bounds
the collapse at the limit. -/
theorem psi_limit_le (s : Supply) (k e bound : O) (he : IsLimit e)
    (h : ∀ e', e' < e → psi s k e' ≤ bound) : psi s k e ≤ bound := by
  classical
  have hex : ∃ xi, ∀ e', e' < e → psi s k e' ≤ xi := ⟨bound, h⟩
  have hspec := least_spec _ hex
  generalize least (fun xi => ∀ e', e' < e → psi s k e' ≤ xi) hex = sigma at hspec
  have hsk : sigma ≤ k := by
    apply (not_lt_iff_le _ _).mp
    intro hks
    exact hspec.2 k hks (fun e' _ => psi_le s k e')
  have hsb : sigma ≤ bound := by
    apply (not_lt_iff_le _ _).mp
    intro hbs
    exact hspec.2 bound hbs h
  have hsig : ∀ x, x < sigma → ∃ e', e' < e ∧ x < psi s k e' := by
    intro x hx
    apply Classical.byContradiction
    intro hnot
    apply hspec.2 x hx
    intro e' he'
    apply (not_lt_iff_le _ _).mp
    intro hlt
    exact hnot ⟨e', he', hlt⟩
  apply le_trans _ hsb
  apply psi_min s k e sigma
  refine ⟨hsk, fun x hx hxk => ?_⟩
  obtain ⟨e', he', hx'⟩ := C_limit_stage s k e sigma he hsig x hx
  exact lt_of_lt_of_le (psi_closed s k e' x hx' hxk) (hspec.1 e' he')

/-- At a successor jump of the collapse, the earlier argument belongs to
its own defining closure. -/
theorem argument_mem_of_psi_succ_gt (s : Supply) (k a : O)
    (h : psi s k a < psi s k (succ a)) : C s a (psi s k a) a := by
  apply Classical.byContradiction
  intro hnot
  apply (not_lt_iff_le _ _).mpr _ h
  apply psi_min s k (succ a) (psi s k a)
  exact ⟨psi_le s k a, fun x hx hxk =>
    psi_closed s k a x (C_successor_of_argument_not_mem s a _ hnot x hx) hxk⟩

/-- The least argument whose collapse exceeds `x` is zero or a successor,
and at a successor the earlier argument satisfies the argument condition. -/
theorem least_exceeding_argument (s : Supply) (k x e : O) (he : x < psi s k e)
    (hmin : ∀ e', e' < e → psi s k e' ≤ x) :
    e = 0 ∨ ∃ e', e = succ e' ∧ psi s k e' ≤ x ∧ C s e' (psi s k e') e' := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · by_cases hs : ∃ e', e = succ e'
    · obtain ⟨e', rfl⟩ := hs
      have hle := hmin e' (lt_succ_self e')
      exact Or.inr ⟨e', rfl, hle, argument_mem_of_psi_succ_gt s k e' (lt_of_le_of_lt hle he)⟩
    · exact False.elim ((not_lt_iff_le _ _).mpr (psi_limit_le s k e x ⟨h0, hs⟩ hmin) he)

end
end OCF.Denis
