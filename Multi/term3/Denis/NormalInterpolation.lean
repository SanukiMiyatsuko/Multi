import Multi.term3.Denis.SeededDiagonal

/-! Interpolation by admissible first-index collapses. The input bound is
a represented ordinal, not an arbitrary ordinal; no density assumption
is silently made here. -/

namespace OCF.Denis
open Ordinal

theorem C_first_successor_argument (s : Supply) (a : O)
    (ha : C s a (psi s (I s 0 0) a) a) :
    C s (succ a) (psi s (I s 0 0) (succ a)) (succ a) := by
  have haa : C s (succ a) (psi s (I s 0 0) (succ a)) a :=
    C_mono_seed s _ _ _ (psi_mono s _ _ _ (Or.inl (lt_succ_self a))) a
      (C_mono_argument s _ _ _ (Or.inl (lt_succ_self a)) a ha)
  have hpos := lt_of_le_of_lt (zero_le a) (lt_succ_self a)
  have hone := C_finite s (succ a) (psi s (I s 0 0) (succ a)) hpos 1
  have h := C_add s _ _ a (succ 0) haa hone
  rw [add_succ, add_zero] at h
  exact h

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem normal_leading_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    IsNormal s t.leading := by
  cases ht with
  | zero => exact .zero
  | index hr hb hrl hbl => exact .index hr hb hrl hbl
  | collapse hk ha hreg harg => exact .collapse hk ha hreg harg
  | @sum a b ha hb hap hp hbpos hhead =>
    change IsNormal s a.leading
    rw [leading_eq_of_principal a hap]
    exact ha

theorem normal_leading_isPrincipal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hne : t ≠ .zero) : t.leading.isPrincipal := by
  cases ht with
  | zero => exact False.elim (hne rfl)
  | index | collapse => trivial
  | @sum a b ha hb hap hp hbpos hhead =>
    change a.leading.isPrincipal
    rw [leading_eq_of_principal a hap]
    exact hap

theorem normal_lt_repeat_leading (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (hne : t ≠ .zero) : ∃ n, denote s t < OCF.Denis.repeatAdd (denote s t.leading) n := by
  revert hne
  induction ht with
  | zero => exact fun h => False.elim (h rfl)
  | @index r b hr hb hrl hbl ihr ihb =>
    intro hne
    have hp := normal_denote_pos s (.I r b) (.index hr hb hrl hbl) hne
    refine ⟨2, ?_⟩
    simpa only [Term.leading, OCF.Denis.repeatAdd, add_zero] using add_lt_add_right (denote s (.I r b)) hp
  | @collapse k a hk ha hreg harg ihk iha =>
    intro hne
    have hp := normal_denote_pos s (.psi k a) (.collapse hk ha hreg harg) hne
    refine ⟨2, ?_⟩
    simpa only [Term.leading, OCF.Denis.repeatAdd, add_zero] using add_lt_add_right (denote s (.psi k a)) hp
  | @sum a b ha hb hap hp hbpos hhead iha ihb =>
    intro _
    change ∃ n, denote s a + denote s b < OCF.Denis.repeatAdd (denote s a.leading) n
    rw [leading_eq_of_principal a hap]
    rcases hhead with hhead | hhead
    · have hbl := normal_lt_of_leading_lt s b hb _ hp hhead
      refine ⟨2, ?_⟩
      simpa only [OCF.Denis.repeatAdd, add_zero] using add_lt_add_right (denote s a) hbl
    · have hbne : b ≠ .zero := by
        intro heq
        rw [heq] at hbpos
        exact OCF.Ordinal.lt_irrefl _ hbpos
      obtain ⟨n, hn⟩ := ihb hbne
      rw [hhead] at hn
      exact ⟨n + 1, add_lt_add_right (denote s a) hn⟩

theorem normal_interpolation (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : OCF.Denis.UncountableRegular r) (t : Term) (ht : IsNormal s t)
    (hlt : denote s t < OCF.Denis.psi s (OCF.Denis.I s 0 0) r) :
    ∃ c, Represented s c ∧ c < r ∧ denote s t < OCF.Denis.psi s (OCF.Denis.I s 0 0) c ∧
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) c := by
  classical
  by_cases hz : t = .zero
  · subst t
    refine ⟨succ 0, ⟨one, one_isNormal s, denote_one s⟩,
      OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.finite_lt_omega 1) hr.1, ?_, ?_⟩
    · rw [OCF.Denis.psi_first_one]
      exact OCF.Denis.finite_lt_omega 0
    · rw [OCF.Denis.psi_first_one]
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.finite_lt_omega 1)
  have hhn := normal_leading_normal s t ht
  have hhp := normal_leading_isPrincipal s t ht hz
  have hhpar := OCF.Ordinal.lt_of_le_of_lt (normal_leading_le s t) hlt
  have hhfirst := OCF.Ordinal.lt_trans _ _ _ hhpar
    (OCF.Denis.psi_lt s _ _ (OCF.Denis.first_regular s))
  obtain ⟨n, hn⟩ := normal_lt_repeat_leading s t ht hz
  cases heq : t.leading with
  | zero | add => rw [heq] at hhp; exact False.elim hhp
  | I q b =>
    rw [heq] at hhfirst
    exact False.elim (OCF.Ordinal.lt_irrefl _
      (OCF.Ordinal.lt_of_le_of_lt (OCF.Denis.I_lower_bound s (denote s q) (denote s b)) hhfirst))
  | psi k a =>
    rw [heq] at hhn hhpar hhfirst hn
    cases hhn with
    | collapse hk ha hreg harg =>
      have hkfirst := OCF.Denis.index_eq_first_of_psi_lt_first s (denote s k) (denote s a) hreg hhfirst
      change OCF.Denis.psi s (denote s k) (denote s a) < _ at hhpar
      change denote s t < OCF.Denis.repeatAdd (OCF.Denis.psi s (denote s k) (denote s a)) n at hn
      rw [hkfirst] at hhpar hn harg
      have har : denote s a < r := by
        rcases OCF.Ordinal.lt_total (denote s a) r with h | h | h
        · exact h
        · rw [h] at hhpar; exact False.elim (OCF.Ordinal.lt_irrefl _ hhpar)
        · exact False.elim (OCF.Ordinal.lt_irrefl _
            (OCF.Ordinal.lt_of_lt_of_le hhpar (OCF.Denis.psi_mono s _ _ _ (Or.inl h))))
      refine ⟨succ (denote s a), represented_succ s _ ⟨a, ha, rfl⟩,
        OCF.Denis.regular_succ_lt hr har, ?_, OCF.Denis.C_first_successor_argument s _ harg⟩
      rw [OCF.Denis.psi_first_successor_eq_repeat_sup s _ harg]
      exact OCF.Ordinal.lt_of_lt_of_le hn (le_sup _ n)

theorem represented_interpolation (s : OCF.Denis.Supply) (r x : OCF.Denis.O)
    (hr : OCF.Denis.UncountableRegular r) (hx : Represented s x)
    (hlt : x < OCF.Denis.psi s (OCF.Denis.I s 0 0) r) :
    ∃ c, Represented s c ∧ c < r ∧ x < OCF.Denis.psi s (OCF.Denis.I s 0 0) c ∧
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) c := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact normal_interpolation s r hr t ht hlt

end
end T.Correspondence.Denis.Covering
