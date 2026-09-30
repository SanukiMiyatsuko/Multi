import Multi.term3.Denis.ZeroIndexNormalization

/-! A normal collapse with a missing index-membership condition can
be replaced by a smaller normal collapse of the same value. The
argument may change to an earlier argument already in a subterm.
Iterating gives a proper presentation for every normal collapse. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_not_uncountableRegular (s : Supply) (k a : O) :
    ¬ UncountableRegular (psi s k a) := by
  intro hp
  have h := psi_lt s (psi s k a) a hp
  rw [psi_index_idempotent] at h
  exact lt_irrefl _ h

theorem psi_le_at_index_of_value_le (s : Supply) (k l a : O) (hvalue : psi s l a ≤ k) :
    psi s l a ≤ psi s k a := by
  rcases lt_total l k with h | h | h
  · exact psi_mono_index s l k a (Or.inl h)
  · rw [h]
    exact le_refl _
  · exact Or.inr (psi_index_plateau s k l a hvalue (Or.inl h)).symm

theorem psi_eq_of_earlier_between (s : Supply) (k l a b : O)
    (hba : b ≤ a) (hlo : psi s k a ≤ psi s l b) (hhi : psi s l b < k) :
    psi s k a = psi s l b :=
  le_antisymm hlo (le_trans (psi_le_at_index_of_value_le s k l b (Or.inl hhi)) (psi_mono s k b a hba))

theorem psi_retarget_of_between (s : Supply) (k l a b : O)
    (hab : a ≤ b) (hlo : psi s k a ≤ psi s l b) (hhi : psi s l b < k) :
    psi s k a = psi s l a := by
  rcases lt_total k l with h | h | h
  · exact psi_index_plateau s k l a
      (le_trans (psi_mono s l a b hab) (Or.inl hhi)) (Or.inl h)
  · rw [h]
  · exact (psi_index_plateau s l k a (le_trans hlo (psi_le s l b)) (Or.inl h)).symm

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering.CollapseNormalization
open OCF.Ordinal
open ZeroIndex (Subterm)
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A normal regular-valued term is syntactically an I term. A
collapse cannot itself be regular, by index idempotence and psi_lt. -/
theorem normal_regular_is_index (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.UncountableRegular (denote s k)) : ∃ r b, k = .I r b := by
  cases hk with
  | zero => exact False.elim (not_lt_zero _ (OCF.Denis.regular_pos hreg))
  | @index r b hr hb hrl hbl => exact ⟨r, b, rfl⟩
  | collapse => exact False.elim (OCF.Denis.psi_not_uncountableRegular s _ _ hreg)
  | @sum u v hu hv hup hp hvpos hhead =>
    have hkp : AddPrincipal (denote s (.add u v)) := fun _ _ hx hy => OCF.Denis.regular_add_closed hreg hx hy
    have huval : denote s u < denote s (.add u v) := by
      simpa only [Denis.denote, add_zero] using add_lt_add_right (denote s u) hvpos
    have hvval := normal_lt_of_leading_lt s v hv _ hkp (OCF.Ordinal.lt_of_le_of_lt hhead huval)
    exact False.elim (OCF.Ordinal.lt_irrefl _ (hkp _ _ huval hvval))

theorem collapse_support_at (s : OCF.Denis.Supply) (k a : OCF.Denis.O) (hk : 0 < k)
    (t : Term) (ht : IsNormal s t) (hlo : OCF.Denis.psi s k a ≤ denote s t) (hhi : denote s t < k) :
    ∃ l b, Subterm (.psi l b) t ∧ IsNormal s (.psi l b) ∧
      OCF.Denis.psi s k a ≤ denote s (.psi l b) ∧ denote s (.psi l b) < k := by
  classical
  induction ht with
  | zero =>
    exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.psi_pos s k a hk) hlo))
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    by_cases hul : denote s u < OCF.Denis.psi s k a
    · by_cases hvl : denote s v < OCF.Denis.psi s k a
      · exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_le_of_lt hlo
          (OCF.Denis.psi_closed s k a _ (OCF.Denis.C_add s a _ _ _
            (OCF.Denis.C_seed s a _ _ hul) (OCF.Denis.C_seed s a _ _ hvl)) hhi)))
      · obtain ⟨l, b, hs, hn, hl, hh⟩ := ihv ((not_lt_iff_le _ _).mp hvl)
          (OCF.Ordinal.lt_of_le_of_lt (right_le_add _ _) hhi)
        exact ⟨l, b, .addRight hs, hn, hl, hh⟩
    · obtain ⟨l, b, hs, hn, hl, hh⟩ := ihu ((not_lt_iff_le _ _).mp hul)
        (OCF.Ordinal.lt_of_le_of_lt (le_add _ _) hhi)
      exact ⟨l, b, .addLeft hs, hn, hl, hh⟩
  | @index r b hr hb hrl hbl ihr ihb =>
    by_cases hrr : denote s r < OCF.Denis.psi s k a
    · by_cases hbb : denote s b < OCF.Denis.psi s k a
      · exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_le_of_lt hlo
          (OCF.Denis.psi_closed s k a _ (OCF.Denis.C_index s a _ _ _
            (OCF.Denis.C_seed s a _ _ hrr) (OCF.Denis.C_seed s a _ _ hbb)) hhi)))
      · obtain ⟨l, c, hs, hn, hl, hh⟩ := ihb ((not_lt_iff_le _ _).mp hbb)
          (OCF.Ordinal.lt_trans _ _ _ hbl hhi)
        exact ⟨l, c, .indexArgument hs, hn, hl, hh⟩
    · obtain ⟨l, c, hs, hn, hl, hh⟩ := ihr ((not_lt_iff_le _ _).mp hrr)
        (OCF.Ordinal.lt_trans _ _ _ hrl hhi)
      exact ⟨l, c, .indexRank hs, hn, hl, hh⟩
  | @collapse l b hl hb hreg harg _ _ =>
    exact ⟨l, b, .refl _, .collapse hl hb hreg harg, hlo, hhi⟩

/-- Either reuse a collapse subterm with an earlier argument, or
retarget the original argument to the subterm's smaller index term. -/
theorem smaller_of_index_not_mem (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a))
    (hnot : ¬ OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a)) (denote s k)) :
    ∃ l b, IsNormal s (.psi l b) ∧ denote s (.psi l b) = denote s (.psi k a) ∧
      sizeOf (Term.psi l b) < sizeOf (Term.psi k a) := by
  classical
  cases hn with
  | collapse hk ha hreg harg =>
    obtain ⟨r, b, rfl⟩ := normal_regular_is_index s k hk (OCF.Denis.regularIndex_regular s _ hreg)
    cases hk with
    | index hr hb hrl hbl =>
      have hrr : denote s r < OCF.Denis.psi s (denote s (.I r b)) (denote s a) :=
        OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.rank_lt_psi_of_first_le s _ _ (normal_rankBounded s r hr)
          (OCF.Denis.I_mono s _ (zero_le _))) (OCF.Denis.psi_mono s _ 0 _ (zero_le _))
      have hbb : OCF.Denis.psi s (denote s (.I r b)) (denote s a) ≤ denote s b := by
        apply (not_lt_iff_le _ _).mp
        intro hbb
        exact hnot (OCF.Denis.C_index s _ _ _ _ (OCF.Denis.C_seed s _ _ _ hrr) (OCF.Denis.C_seed s _ _ _ hbb))
      obtain ⟨l, c, hs, hnc, hlo, hhi⟩ := collapse_support_at s (denote s (.I r b)) (denote s a)
        (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ hreg)) b hb hbb hbl
      by_cases hca : denote s c ≤ denote s a
      · refine ⟨l, c, hnc, (OCF.Denis.psi_eq_of_earlier_between s _ _ _ _ hca hlo hhi).symm, ?_⟩
        have hsize := hs.size_le
        simp at hsize ⊢
        omega
      · have hac : denote s a ≤ denote s c := by
          rcases OCF.Ordinal.lt_total (denote s a) (denote s c) with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact False.elim (hca (Or.inl h))
        have heq := OCF.Denis.psi_retarget_of_between s _ _ _ _ hac hlo hhi
        cases hnc with
        | collapse hl hc hlreg hcarg =>
          refine ⟨l, a, .collapse hl ha hlreg ?_, heq.symm, ?_⟩
          · change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s l) (denote s a)) (denote s a)
            rw [← heq]
            exact harg
          · have hsize := hs.size_le
            simp at hsize ⊢
            omega

def Proper (s : OCF.Denis.Supply) (t : Term) : Prop :=
  ∃ r b a, t = .psi (.I r b) a ∧ IsNormal s t ∧
    OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s (.I r b)) (denote s a)) (denote s (.I r b))

theorem Proper.normal {s : OCF.Denis.Supply} {t : Term} (h : Proper s t) : IsNormal s t := by
  obtain ⟨_, _, _, _, hn, _⟩ := h
  exact hn

theorem Proper.isCollapse {s : OCF.Denis.Supply} {t : Term} (h : Proper s t) : ∃ k a, t = .psi k a := by
  obtain ⟨r, b, a, heq, _, _⟩ := h
  exact ⟨.I r b, a, heq⟩

theorem exists_proper (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) :
    ∃ u, Proper s u ∧ denote s u = denote s t ∧ sizeOf u ≤ sizeOf t := by
  classical
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    obtain ⟨k, a, rfl⟩ := hc
    by_cases hmem : OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a)) (denote s k)
    · cases ht with
      | collapse hk ha hreg harg =>
        obtain ⟨r, b, rfl⟩ := normal_regular_is_index s k hk (OCF.Denis.regularIndex_regular s _ hreg)
        exact ⟨_, ⟨r, b, a, rfl, .collapse hk ha hreg harg, hmem⟩, rfl, Nat.le_refl _⟩
    · obtain ⟨l, b, hn, heq, hsize⟩ := smaller_of_index_not_mem s k a ht hmem
      obtain ⟨u, hu, hueq, husize⟩ := ih (.psi l b) hsize hn ⟨l, b, rfl⟩
      exact ⟨u, hu, hueq.trans heq, Nat.le_trans husize (Nat.le_of_lt hsize)⟩

def normalize (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) : Term :=
  if Proper s t then t else Classical.choose (exists_proper s t ht hc)

theorem normalize_spec (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) :
    Proper s (normalize s t ht hc) ∧ denote s (normalize s t ht hc) = denote s t ∧
      sizeOf (normalize s t ht hc) ≤ sizeOf t := by
  classical
  unfold normalize
  split
  · rename_i h
    exact ⟨h, rfl, Nat.le_refl _⟩
  · exact Classical.choose_spec (exists_proper s t ht hc)

theorem normalize_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) : IsNormal s (normalize s t ht hc) :=
  (normalize_spec s t ht hc).1.normal

theorem normalize_isCollapse (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) : ∃ k a, normalize s t ht hc = .psi k a :=
  (normalize_spec s t ht hc).1.isCollapse

theorem normalize_of_proper (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) (hp : Proper s t) : normalize s t ht hc = t := by
  unfold normalize
  rw [ite_eq_left hp]

theorem normalize_idempotent (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) :
    normalize s (normalize s t ht hc) (normalize_normal s t ht hc) (normalize_isCollapse s t ht hc) =
      normalize s t ht hc :=
  normalize_of_proper s _ _ _ (normalize_spec s t ht hc).1

/-- Proper presentations have the same ordinal parameters whenever
their values agree. This is not uniqueness of the raw syntax. -/
theorem parameters_unique (s : OCF.Denis.Supply) (r b a q c d : Term)
    (hn : IsNormal s (.psi (.I r b) a)) (hm : IsNormal s (.psi (.I q c) d))
    (hk : OCF.Denis.C s (denote s a) (denote s (.psi (.I r b) a)) (denote s (.I r b)))
    (hl : OCF.Denis.C s (denote s d) (denote s (.psi (.I q c) d)) (denote s (.I q c)))
    (heq : denote s (.psi (.I r b) a) = denote s (.psi (.I q c) d)) :
    denote s r = denote s q ∧ denote s b = denote s c ∧ denote s a = denote s d := by
  cases hn with
  | collapse hI ha hreg harg =>
    cases hm with
    | collapse hJ hd hjreg hdarg =>
      obtain ⟨hij, had⟩ := OCF.Denis.psi_normal_parameters_unique s _ _ _ _ hreg hjreg hk harg hl hdarg heq
      cases hI with
      | index hr hb hrl hbl =>
        cases hJ with
        | index hq hc hql hcl =>
          obtain ⟨hrq, hbc⟩ := OCF.Denis.I_normal_injective s _ _ _ _ hbl hcl hij
          exact ⟨hrq, hbc, had⟩

end
end T.Correspondence.Denis.Covering.CollapseNormalization
