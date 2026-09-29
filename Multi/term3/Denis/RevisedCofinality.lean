import Multi.term3.Denis.RevisedNormal

/-! Actual ordinal cofinality for the repaired expansion. Density is
proved for the established collapsing examples. A separate theorem
records why uncountable regular domains cannot use an omega sequence.
-/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem dense_of_normal_sequence (s : OCF.Denis.Supply) (a : OCF.Denis.O) (f : Nat → OCF.Denis.O)
    (hf : OCF.Denis.FundamentalSequence a f) (hn : ∀ n, Represented s (f n)) : DenseBelow s a := by
  intro x hx
  obtain ⟨n, hn'⟩ := hf.cofinal x hx
  exact ⟨f n, hn n, hn', hf.below n⟩

theorem dense_iff_revised_cofinal (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : 0 < a) :
    DenseBelow s a ↔ ∀ x, x < a → ∃ n, x < revisedValue s a n := by
  constructor
  · intro h
    exact (revised_fundamentalSequence_of_dense s a ha h).cofinal
  · intro h x hx
    obtain ⟨n, hn⟩ := h x hx
    exact ⟨_, revisedValue_represented s a n, hn, revisedValue_lt s a ha n⟩

def finiteTerm (n : Nat) : Term := Source2019.repeatTerm one n

theorem denote_finiteTerm (s : OCF.Denis.Supply) (n : Nat) :
    denote s (finiteTerm n) = OCF.Denis.finite n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => exact denote_one s
    | succ n =>
      change denote s one + denote s (finiteTerm (n + 1)) = _
      rw [denote_one, ih]
      change OCF.Denis.finite 1 + OCF.Denis.finite (n + 1) = _
      rw [OCF.Denis.finite_add]
      congr 1
      omega

theorem finiteTerm_leading (n : Nat) : (finiteTerm (n + 1)).leading = one := by
  cases n <;> rfl

theorem finiteTerm_normal (s : OCF.Denis.Supply) (n : Nat) : IsNormal s (finiteTerm n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    cases n with
    | zero => exact one_isNormal s
    | succ n =>
      apply IsNormal.sum (one_isNormal s) ih (by trivial)
      · rw [denote_one]; exact succ_zero_principal
      · rw [denote_finiteTerm]
        exact OCF.Denis.finite_strict (show 0 < n + 1 by omega)
      · rw [finiteTerm_leading]
        exact le_refl _

theorem finite_represented (s : OCF.Denis.Supply) (n : Nat) : Represented s (OCF.Denis.finite n) :=
  ⟨finiteTerm n, finiteTerm_normal s n, denote_finiteTerm s n⟩

theorem omega_dense (s : OCF.Denis.Supply) : DenseBelow s OCF.Denis.omega :=
  dense_of_normal_sequence s _ _ OCF.Denis.omega_fundamentalSequence (finite_represented s)

theorem revised_omega_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence OCF.Denis.omega (revisedValue s OCF.Denis.omega) :=
  revised_fundamentalSequence_of_dense s _ (OCF.Denis.finite_lt_omega 0) (omega_dense s)

theorem epsilon_dense (s : OCF.Denis.Supply) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0)) := by
  apply dense_of_normal_sequence s _ _ (OCF.Denis.tower_fundamentalSequence s 1)
  intro n
  exact ⟨iterate exp .zero (n + 1), tower_isNormal s (n + 1), denote_iterate_exp s (n + 1)⟩

theorem revised_epsilon_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s))) (epsilon_dense s)

theorem cardFixed_dense (s : OCF.Denis.Supply) : DenseBelow s (OCF.Denis.obstructionBase s) := by
  apply dense_of_normal_sequence s _ _ (OCF.Denis.first_inaccessible_zero_fundamentalSequence s)
  intro n
  exact ⟨indexIterTerm .zero n, indexIterTerm_isNormal s .zero .zero n, denote_indexIterTerm s .zero n⟩

/-- In particular, the parent from the rule-10.5 counterexample now has
a valid sequence, with no change to its OCF value. -/
theorem revised_obstruction_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (OCF.Denis.obstructionValue s)
      (revisedValue s (OCF.Denis.obstructionValue s)) := by
  rw [OCF.Denis.obstructionValue_eq_base]
  apply revised_fundamentalSequence_of_dense s _ _ (cardFixed_dense s)
  exact OCF.Denis.psi_pos s _ _
    (OCF.Denis.regular_pos (OCF.Denis.inaccessible_regular (OCF.Denis.first_inaccessible s (succ 0))))

theorem collapseI_dense (s : OCF.Denis.Supply) : DenseBelow s (denote s collapseI) := by
  apply dense_of_normal_sequence s _ _ (collapseISeq_fundamentalSequence s)
  intro n
  exact ⟨collapseISeq n, collapseISeq_isNormal s n, rfl⟩

theorem revised_collapseI_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (denote s collapseI) (revisedValue s (denote s collapseI)) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s))) (collapseI_dense s)

theorem represented_I (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) : Represented s (OCF.Denis.I s r b) := by
  obtain ⟨rt, hrt, rfl⟩ := hr
  obtain ⟨bt, hbt, rfl⟩ := hb
  rcases OCF.Denis.rank_le_I s (denote s rt) (denote s bt) with hr | hr
  · rcases OCF.Denis.index_le_I s (denote s rt) (denote s bt) with hb | hb
    · exact ⟨.I rt bt, .index hrt hbt hr hb, rfl⟩
    · exact ⟨bt, hbt, hb⟩
  · exact ⟨rt, hrt, hr⟩

theorem I_dense_of_normal_sequence (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (f : Nat → OCF.Denis.O)
    (hf : OCF.Denis.FundamentalSequence a f) (hn : ∀ n, Represented s (f n)) :
    DenseBelow s (OCF.Denis.I s r a) :=
  dense_of_normal_sequence s _ _ (OCF.Denis.I_fundamentalSequence s r a f hf)
    (fun n => represented_I s r (f n) hr (hn n))

/-- Uncountable regular ordinals require ordinal-indexed sequences. A
countable enumeration of finite normal terms cannot be cofinal there. -/
theorem not_dense_regular (s : OCF.Denis.Supply) (k : OCF.Denis.O)
    (hk : OCF.Denis.UncountableRegular k) : ¬ DenseBelow s k := by
  intro hd
  have ha := OCF.Denis.regular_pos hk
  obtain ⟨bound, hb, hfb⟩ := OCF.Denis.small_nat hk (revisedValue s k) (revisedValue_lt s k ha)
  obtain ⟨n, hn⟩ := (dense_iff_revised_cofinal s k ha).mp hd bound hb
  exact OCF.Ordinal.lt_asymm hn (hfb n)

end
end T.Correspondence.Denis.Covering
