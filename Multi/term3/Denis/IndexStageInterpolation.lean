import Multi.term3.Denis.NormalStageInterpolation

/-! Represented bounds below a limit of I can be exceeded at a
represented earlier argument. This supplies the inverse direction
needed to preserve cofinality among finite normal notations. -/

namespace OCF.Denis
open Ordinal

theorem I_limit_le_of_forall (s : Supply) (r a x : O) (ha : IsLimit a)
    (h : ∀ c, c < a → I s r c ≤ x) : I s r a ≤ x := by
  rw [I_limit s r a ha.1 ha.2]
  exact (sup_le_iff _ _).mpr (fun i => h _ (initial_lt a i))

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem combine_represented_stages (s : OCF.Denis.Supply) (a x y : OCF.Denis.O)
    (f : OCF.Denis.O → OCF.Denis.O) (hm : ∀ c d, c ≤ d → f c ≤ f d)
    (hx : ∃ c, Represented s c ∧ c < a ∧ x < f c)
    (hy : ∃ c, Represented s c ∧ c < a ∧ y < f c) :
    ∃ c, Represented s c ∧ c < a ∧ x < f c ∧ y < f c := by
  obtain ⟨c, hc, hca, hxc⟩ := hx
  obtain ⟨d, hd, hda, hyd⟩ := hy
  rcases OCF.Ordinal.lt_total c d with h | h | h
  · exact ⟨d, hd, hda, OCF.Ordinal.lt_of_lt_of_le hxc (hm c d (Or.inl h)), hyd⟩
  · exact ⟨d, hd, hda, h ▸ hxc, hyd⟩
  · exact ⟨c, hc, hca, hxc, OCF.Ordinal.lt_of_lt_of_le hyd (hm d c (Or.inl h))⟩

theorem normal_limit_index_interpolation (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : OCF.Denis.IsLimit a)
    (t : Term) (ht : IsNormal s t) (hlt : denote s t < OCF.Denis.I s r a) :
    ∃ c, Represented s c ∧ c < a ∧ denote s t < OCF.Denis.I s r c := by
  classical
  have hrank : r < OCF.Denis.I s r 0 := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    rw [OCF.Denis.I_zero]
    exact OCF.Denis.rank_lt_first_of_bounded s _ (normal_rankBounded s rt hrt)
  have small (x : OCF.Denis.O) (hx : Represented s x) (hxa : x < a) :
      ∃ c, Represented s c ∧ c < a ∧ x < OCF.Denis.I s r c :=
    ⟨succ x, represented_succ s x hx, OCF.Denis.succ_lt_limit ha hxa,
      OCF.Ordinal.lt_of_lt_of_le (lt_succ_self x) (OCF.Denis.index_le_I s r (succ x))⟩
  induction ht with
  | zero =>
    exact ⟨0, ⟨.zero, .zero, rfl⟩, (zero_lt_iff_ne_zero a).mpr ha.1,
      OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨r, rfl⟩))⟩
  | @sum p b hp hb hpp hpv hbpos hhead ihp ihb =>
    obtain ⟨c, hc, hca, hpc, hbc⟩ := combine_represented_stages s a _ _ (OCF.Denis.I s r)
      (fun _ _ h => OCF.Denis.I_mono s r h)
      (ihp (OCF.Ordinal.lt_of_le_of_lt (le_add _ _) hlt))
      (ihb (OCF.Ordinal.lt_of_le_of_lt (right_le_add _ _) hlt))
    exact ⟨c, hc, hca, OCF.Denis.I_addPrincipal s r c _ _ hpc hbc⟩
  | @index q b hq hb hql hbl ihq ihb =>
    rcases OCF.Ordinal.lt_total (denote s q) r with hqr | hqr | hrq
    · obtain ⟨c, hc, hca, hbc⟩ := ihb (OCF.Ordinal.lt_trans _ _ _ hbl hlt)
      exact ⟨c, hc, hca, OCF.Denis.I_lower_rank_closed s _ r c _ hqr hbc⟩
    · have hba : denote s b < a := by
        apply Classical.byContradiction
        intro hn
        have h := OCF.Denis.I_mono s r ((not_lt_iff_le _ _).mp hn)
        change OCF.Denis.I s (denote s q) (denote s b) < _ at hlt
        rw [hqr] at hlt
        exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hlt h)
      refine ⟨succ (denote s b), represented_succ s _ ⟨b, hb, rfl⟩, OCF.Denis.succ_lt_limit ha hba, ?_⟩
      change OCF.Denis.I s (denote s q) _ < _
      rw [hqr]
      exact OCF.Denis.I_strict s r (lt_succ_self _)
    · apply small _ ⟨.I q b, .index hq hb hql hbl, rfl⟩
      apply Classical.byContradiction
      intro hn
      have hax := (not_lt_iff_le _ _).mp hn
      have hbound := OCF.Denis.I_limit_le_of_forall s r a (denote s (.I q b)) ha
        (fun c hc => Or.inl (OCF.Denis.I_lower_rank_closed s r (denote s q) (denote s b) c hrq
          (OCF.Ordinal.lt_of_lt_of_le hc hax)))
      exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hlt hbound)
  | @collapse k d hk hd hreg harg ihk ihd =>
    by_cases hsmall : denote s (.psi k d) < OCF.Denis.I s r 0
    · exact ⟨0, ⟨.zero, .zero, rfl⟩, (zero_lt_iff_ne_zero a).mpr ha.1, hsmall⟩
    have hrx := OCF.Ordinal.lt_of_lt_of_le hrank ((not_lt_iff_le _ _).mp hsmall)
    by_cases hkbound : denote s k < OCF.Denis.I s r a
    · obtain ⟨c, hc, hca, hkc⟩ := ihk hkbound
      exact ⟨c, hc, hca, OCF.Ordinal.lt_trans _ _ _
        (OCF.Denis.psi_lt s _ _ (OCF.Denis.regularIndex_regular s _ hreg)) hkc⟩
    apply small _ ⟨.psi k d, .collapse hk hd hreg harg, rfl⟩
    apply Classical.byContradiction
    intro hn
    have hax := (not_lt_iff_le _ _).mp hn
    have hparentk := (not_lt_iff_le _ _).mp hkbound
    have hbound := OCF.Denis.I_limit_le_of_forall s r a (denote s (.psi k d)) ha (fun c hc =>
      Or.inl (OCF.Denis.psi_closed s (denote s k) (denote s d) (OCF.Denis.I s r c)
        (OCF.Denis.C_index s _ _ r c (OCF.Denis.C_seed s _ _ _ hrx)
          (OCF.Denis.C_seed s _ _ _ (OCF.Ordinal.lt_of_lt_of_le hc hax)))
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.I_strict s r hc) hparentk)))
    exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hlt hbound)

theorem represented_limit_index_interpolation (s : OCF.Denis.Supply) (r a x : OCF.Denis.O)
    (hr : Represented s r) (ha : OCF.Denis.IsLimit a)
    (hx : Represented s x) (hlt : x < OCF.Denis.I s r a) :
    ∃ c, Represented s c ∧ c < a ∧ x < OCF.Denis.I s r c := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact normal_limit_index_interpolation s r a hr ha t ht hlt

end
end T.Correspondence.Denis.Covering
