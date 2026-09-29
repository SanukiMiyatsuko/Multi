import Multi.term3.Denis.SuccessorSequence

/-! Unconditional density for every normal limit up to the first diagonal
collapse. This is an interval theorem, not merely a list of examples. -/

namespace OCF.Denis
open Ordinal

theorem right_isLimit_of_add_isLimit (a b : O) (hb : b ≠ 0) (h : IsLimit (a + b)) :
    IsLimit b := by
  refine ⟨hb, ?_⟩
  rintro ⟨c, rfl⟩
  exact h.2 ⟨a + c, add_succ a c⟩

theorem argument_lt_first_of_collapse_lt_diagonal (s : Supply) (a : O)
    (h : psi s (I s 0 0) a < psi s (I s 0 0) (I s 0 0)) : a < I s 0 0 := by
  rcases lt_total a (I s 0 0) with ha | ha | ha
  · exact ha
  · rw [ha] at h; exact False.elim (lt_irrefl _ h)
  · exact False.elim (lt_irrefl _ (lt_of_lt_of_le h (psi_mono s _ _ _ (Or.inl ha))))

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem psi_first_normal_limit_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hak : a < OCF.Denis.I s 0 0)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) a)
    (hd : DenseBelow s a) : DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) := by
  let f := revisedValue s a
  have hf := revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd
  have hargs (n : Nat) : OCF.Denis.C s (f n) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (f n)) (f n) :=
    OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f n) hak harg (hf.below n))
  apply dense_of_normal_sequence s _ _ (OCF.Denis.psi_fundamentalSequence s _ a f
    (Or.inl ⟨0, rfl⟩) hf (fun _ => OCF.Denis.first_mem_C s _ _) hargs)
  intro n
  exact represented_psi_of_mem s _ (f n) ⟨omega1, omega1_isNormal s, rfl⟩
    (revisedValue_represented s a n) (Or.inl ⟨0, rfl⟩) (hargs n)

theorem normal_dense_below_first_diagonal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hbound : denote s t ≤ OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0))
    (hlim : OCF.Denis.IsLimit (denote s t)) : DenseBelow s (denote s t) := by
  classical
  have htop := OCF.Denis.psi_lt s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0)
    (OCF.Denis.first_regular s)
  revert hbound hlim
  induction ht with
  | zero =>
    intro _ hlim
    exact False.elim (hlim.1 rfl)
  | @index r b hr hb hrl hbl ihr ihb =>
    intro hbound _
    have hlt := OCF.Ordinal.lt_of_le_of_lt hbound htop
    exact False.elim (OCF.Ordinal.lt_irrefl _
      (OCF.Ordinal.lt_of_le_of_lt (OCF.Denis.I_lower_bound s (denote s r) (denote s b)) hlt))
  | @collapse k a hk ha hreg harg ihk iha =>
    intro hbound hlim
    change OCF.Denis.psi s (denote s k) (denote s a) ≤ _ at hbound
    change OCF.Denis.IsLimit (OCF.Denis.psi s (denote s k) (denote s a)) at hlim
    change DenseBelow s (OCF.Denis.psi s (denote s k) (denote s a))
    have heq := OCF.Denis.index_eq_first_of_psi_lt_first s (denote s k) (denote s a) hreg
      (OCF.Ordinal.lt_of_le_of_lt hbound htop)
    rw [heq] at hbound hlim harg ⊢
    rcases hbound with hbound | hbound
    · have hal := OCF.Denis.argument_lt_first_of_collapse_lt_diagonal s (denote s a) hbound
      have ha_lt := OCF.Denis.psi_closed s _ _ _ harg hal
      by_cases haz : denote s a = 0
      · rw [haz, OCF.Denis.psi_first_zero] at hlim
        exact False.elim (hlim.2 ⟨0, rfl⟩)
      by_cases has : ∃ b, denote s a = succ b
      · obtain ⟨b, hb⟩ := has
        have hrep : Represented s (succ b) := ⟨a, ha, hb⟩
        have hbk : b < OCF.Denis.I s 0 0 :=
          OCF.Ordinal.lt_trans _ _ _ (lt_succ_self b) (hb ▸ hal)
        rw [hb] at harg ⊢
        have hprev := OCF.Denis.psi_predecessor_argument_normal s _ b (OCF.Denis.first_regular s) hbk harg
        exact psi_first_successor_dense s b (represented_predecessor s b hrep) hprev
      · have hai : OCF.Denis.IsLimit (denote s a) := ⟨haz, has⟩
        have had := iha (Or.inl (OCF.Ordinal.lt_trans _ _ _ ha_lt hbound)) hai
        exact psi_first_normal_limit_dense s (denote s a) hai hal harg had
    · rw [hbound]
      exact epsilon_dense s
  | @sum a b ha hb hap hp hbpos hhead iha ihb =>
    intro hbound hlim
    change denote s a + denote s b ≤ _ at hbound
    change OCF.Denis.IsLimit (denote s a + denote s b) at hlim
    have hbl := OCF.Denis.right_isLimit_of_add_isLimit _ _ ((zero_lt_iff_ne_zero _).mp hbpos) hlim
    exact add_dense s (denote s a) (denote s b) ⟨a, ha, rfl⟩ hbl
      (ihb (OCF.Ordinal.le_trans (right_le_add _ _) hbound) hbl)

theorem revised_normal_below_first_diagonal_fundamentalSequence (s : OCF.Denis.Supply)
    (t : Term) (ht : IsNormal s t)
    (hbound : denote s t ≤ OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0))
    (hlim : OCF.Denis.IsLimit (denote s t)) :
    OCF.Denis.FundamentalSequence (denote s t) (revisedValue s (denote s t)) :=
  revised_fundamentalSequence_of_dense s _ ((zero_lt_iff_ne_zero _).mpr hlim.1)
    (normal_dense_below_first_diagonal s t ht hbound hlim)

end
end T.Correspondence.Denis.Covering
