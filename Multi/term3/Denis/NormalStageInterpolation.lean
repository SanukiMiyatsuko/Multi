import Multi.term3.Denis.CompositeLimitSequences

/-! Finite normal bounds below a limit collapse can be exceeded at a
represented earlier argument. This is interpolation for represented
bounds; it does not assert that all ordinals below a regular cardinal
are represented by finite terms. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

private theorem combine_stages (s : OCF.Denis.Supply) (k a x y : OCF.Denis.O)
    (hx : ∃ c, Represented s c ∧ c < a ∧ x < OCF.Denis.psi s k c)
    (hy : ∃ c, Represented s c ∧ c < a ∧ y < OCF.Denis.psi s k c) :
    ∃ c, Represented s c ∧ c < a ∧ x < OCF.Denis.psi s k c ∧ y < OCF.Denis.psi s k c := by
  obtain ⟨c, hc, hca, hxc⟩ := hx
  obtain ⟨d, hd, hda, hyd⟩ := hy
  rcases OCF.Ordinal.lt_total c d with h | h | h
  · exact ⟨d, hd, hda, OCF.Ordinal.lt_of_lt_of_le hxc (OCF.Denis.psi_mono s k c d (Or.inl h)), hyd⟩
  · exact ⟨d, hd, hda, h ▸ hxc, hyd⟩
  · exact ⟨c, hc, hca, hxc, OCF.Ordinal.lt_of_lt_of_le hyd (OCF.Denis.psi_mono s k d c (Or.inl h))⟩

theorem normal_limit_collapse_interpolation (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a)
    (t : Term) (ht : IsNormal s t) (hlt : denote s t < OCF.Denis.psi s k a) :
    ∃ c, Represented s c ∧ c < a ∧ denote s t < OCF.Denis.psi s k c := by
  classical
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    have hparent := OCF.Denis.psi_lt s k a (OCF.Denis.regularIndex_regular s k hk)
    cases ht with
    | zero =>
      exact ⟨0, ⟨.zero, .zero, rfl⟩, (zero_lt_iff_ne_zero a).mpr ha.1,
        OCF.Denis.psi_pos s k 0 (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s k hk))⟩
    | @sum p b hp hb hpp hpv hbpos hhead =>
      have hp' := ih p (by change sizeOf p < sizeOf (Term.add p b); simp; omega) hp
        (OCF.Ordinal.lt_of_le_of_lt (le_add _ _) hlt)
      have hb' := ih b (by change sizeOf b < sizeOf (Term.add p b); simp; omega) hb
        (OCF.Ordinal.lt_of_le_of_lt (right_le_add _ _) hlt)
      obtain ⟨c, hc, hca, hpc, hbc⟩ := combine_stages s k a _ _ hp' hb'
      exact ⟨c, hc, hca, OCF.Denis.psi_addPrincipal s k c (OCF.Denis.regularIndex_regular s k hk) _ _ hpc hbc⟩
    | @index r b hr hb hrl hbl =>
      have hr' := ih r (by change sizeOf r < sizeOf (Term.I r b); simp; omega) hr
        (OCF.Ordinal.lt_trans _ _ _ hrl hlt)
      have hb' := ih b (by change sizeOf b < sizeOf (Term.I r b); simp; omega) hb
        (OCF.Ordinal.lt_trans _ _ _ hbl hlt)
      obtain ⟨c, hc, hca, hrc, hbc⟩ := combine_stages s k a _ _ hr' hb'
      exact ⟨c, hc, hca, OCF.Denis.psi_closed s k c _
        (OCF.Denis.C_index s c _ _ _ (OCF.Denis.C_seed s c _ _ hrc) (OCF.Denis.C_seed s c _ _ hbc))
        (OCF.Ordinal.lt_trans _ _ _ hlt hparent)⟩
    | @collapse l d hl hd hreg harg =>
      have hn : IsNormal s (.psi l d) := .collapse hl hd hreg harg
      by_cases hindex : OCF.Denis.C s (denote s d) (denote s (.psi l d)) (denote s l)
      · by_cases hda : denote s d < a
        · let c := succ (denote s d)
          have hval : denote s (.psi l d) ≤ OCF.Denis.psi s k c :=
            OCF.Ordinal.le_trans (OCF.Denis.psi_le_at_index_of_value_le s k (denote s l) (denote s d)
              (Or.inl (OCF.Ordinal.lt_trans _ _ _ hlt hparent)))
              (OCF.Denis.psi_mono s k _ c (Or.inl (lt_succ_self _)))
          have promote (x : OCF.Denis.O)
              (hx : OCF.Denis.C s (denote s d) (denote s (.psi l d)) x) :
              OCF.Denis.C s c (OCF.Denis.psi s k c) x :=
            OCF.Denis.C_mono_seed s c _ _ hval x
              (OCF.Denis.C_mono_argument s _ c _ (Or.inl (lt_succ_self _)) x hx)
          exact ⟨c, represented_succ s _ ⟨d, hd, rfl⟩, OCF.Denis.succ_lt_limit ha hda,
            OCF.Denis.psi_closed s k c _ (OCF.Denis.C_collapse s c _ _ _ (lt_succ_self _) hreg
              (promote _ hindex) (promote _ harg)) (OCF.Ordinal.lt_trans _ _ _ hlt hparent)⟩
        · have had := (not_lt_iff_le _ _).mp hda
          have hlparent : denote s l < OCF.Denis.psi s k a := by
            apply Classical.byContradiction
            intro hnot
            have hv := OCF.Denis.psi_le_at_index_of_value_le s (denote s l) k a
              ((not_lt_iff_le _ _).mp hnot)
            have hv' := OCF.Ordinal.le_trans hv (OCF.Denis.psi_mono s (denote s l) a (denote s d) had)
            exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hlt hv')
          obtain ⟨c, hc, hca, hlc⟩ := ih l
            (by change sizeOf l < sizeOf (Term.psi l d); simp; omega) hl hlparent
          exact ⟨c, hc, hca, OCF.Ordinal.lt_trans _ _ _
            (OCF.Denis.psi_lt s _ _ (OCF.Denis.regularIndex_regular s _ hreg)) hlc⟩
      · obtain ⟨j, b, hb, heq, hsize⟩ := CollapseNormalization.smaller_of_index_not_mem s l d hn hindex
        have h := ih (.psi j b) hsize hb (heq ▸ hlt)
        simpa only [heq] using h

theorem represented_limit_collapse_interpolation (s : OCF.Denis.Supply) (k a x : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a)
    (hx : Represented s x) (hlt : x < OCF.Denis.psi s k a) :
    ∃ c, Represented s c ∧ c < a ∧ x < OCF.Denis.psi s k c := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact normal_limit_collapse_interpolation s k a hk ha t ht hlt

/-- The parent supplies a represented argument at which its index
already belongs to the defining closure. No zero-argument index
membership or countability hypothesis is imposed. -/
theorem proper_index_mem_at_represented_stage (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.IsLimit (denote s a))
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)) :
    ∃ c, Represented s c ∧ c < denote s a ∧
      OCF.Denis.C s c (OCF.Denis.psi s (denote s k) c) (denote s k) := by
  cases hn with
  | collapse hk haN hreg harg =>
    obtain ⟨r, b, rfl⟩ := CollapseNormalization.normal_regular_is_index s k hk
      (OCF.Denis.regularIndex_regular s _ hreg)
    cases hk with
    | index hr hb hrl hbl =>
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ _ _ hrl hbl hK
      have hr' := normal_limit_collapse_interpolation s _ _ hreg ha r hr
        (OCF.Denis.psi_closed s _ _ _ hrC hrl)
      have hb' := normal_limit_collapse_interpolation s _ _ hreg ha b hb
        (OCF.Denis.psi_closed s _ _ _ hbC hbl)
      obtain ⟨c, hc, hca, hrc, hbc⟩ := combine_stages s _ _ _ _ hr' hb'
      exact ⟨c, hc, hca, OCF.Denis.C_index s _ _ _ _
        (OCF.Denis.C_seed s _ _ _ hrc) (OCF.Denis.C_seed s _ _ _ hbc)⟩

theorem proper_regular_below_normalFundamentalSequence (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.UncountableRegular (denote s a))
    (hbound : denote s a < denote s k)
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)) :
    ∃ c, Represented s c ∧ c < denote s a ∧
      NormalFundamentalSequence s (denote s (.psi k a)) (denote s a)
        (fun i => OCF.Denis.psi s (denote s k) (c + i)) := by
  obtain ⟨c, hc, hca, hstage⟩ := proper_index_mem_at_represented_stage s k a hn
    (OCF.Denis.regular_isLimit ha) hK
  cases hn with
  | collapse hk haN hreg harg =>
    refine ⟨c, hc, hca, ?_⟩
    exact psi_normal_limit_tail_normalFundamentalSequence s _ _ _ c hreg ⟨k, hk, rfl⟩
      (OCF.Denis.regular_pos ha) (fun _ _ hx hy => OCF.Denis.regular_add_closed ha hx hy)
      hca hc (fun i => i) (regular_normalFundamentalSequence s _ ha) hbound harg hstage

theorem normal_regularIndex (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hr : OCF.Denis.UncountableRegular (denote s t)) : OCF.Denis.RegularIndex s (denote s t) := by
  obtain ⟨r, b, rfl⟩ := CollapseNormalization.normal_regular_is_index s t ht hr
  cases ht with
  | index hrN hb hrl hbl =>
    rcases OCF.Denis.regular_I_argument s _ _ hbl hr with hz | hs
    · exact Or.inl ⟨denote s r, by change OCF.Denis.I s _ _ = _; rw [hz]⟩
    · obtain ⟨c, hc⟩ := hs
      exact Or.inr ⟨denote s r, c, by change OCF.Denis.I s _ _ = _; rw [hc]⟩

end
end T.Correspondence.Denis.Covering
