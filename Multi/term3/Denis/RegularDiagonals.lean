import Multi.term3.Denis.CountableTails

/-! Normality and repaired cofinality for the diagonal rule at regular
indices constructible at every positive cutoff. Finite I parameters
provide an unconditional two-parameter family of such indices. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem C_finite (s : Supply) (a beta : O) (ha : 0 < a) (n : Nat) : C s a beta (finite n) := by
  have hone : C s a beta (succ 0) := by
    rw [← psi_first_zero s]
    exact C_collapse s a beta (I s 0 0) 0 ha (Or.inl ⟨0, rfl⟩)
      (first_mem_C s a beta) (C_zero s a beta)
  induction n with
  | zero => exact C_zero s a beta
  | succ n ih =>
    have h := C_add s a beta (finite n) (succ 0) ih hone
    rw [add_succ, add_zero] at h
    exact h

theorem finite_parameters_regular (s : Supply) (n m : Nat) :
    RegularIndex s (I s (finite n) (finite m)) := by
  cases m with
  | zero => exact Or.inl ⟨finite n, rfl⟩
  | succ m => exact Or.inr ⟨finite n, finite m, rfl⟩

theorem finite_parameters_mem_C (s : Supply) (n m : Nat) (a beta : O) (ha : 0 < a) :
    C s a beta (I s (finite n) (finite m)) :=
  C_index s a beta _ _ (C_finite s a beta ha n) (C_finite s a beta ha m)

theorem first_lt_finite_parameters (s : Supply) (n m : Nat) (h : 0 < n + m) :
    I s 0 0 < I s (finite n) (finite m) := by
  cases n with
  | zero =>
    have hm : 0 < m := by omega
    exact I_strict s 0 (finite_strict hm)
  | succ n =>
    have hq := first_rank_strict s (finite_strict (show 0 < n + 1 by omega))
    change first s 0 < first s (finite (n + 1)) at hq
    rw [← I_zero s 0, ← I_zero s (finite (n + 1))] at hq
    exact lt_of_lt_of_le hq (I_mono s (finite (n + 1)) (zero_le (finite m)))

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem diagonalIter_represented (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) (hreg : OCF.Denis.RegularIndex s r) (hlarge : OCF.Denis.I s 0 0 < r)
    (hindex : ∀ a b, 0 < a → OCF.Denis.C s a b r) (n : Nat) :
    Represented s (OCF.Denis.diagonalIter s r n) := by
  induction n with
  | zero => exact ⟨one, one_isNormal s, denote_one s⟩
  | succ n ih =>
    exact represented_psi_of_mem s r _ hr ih hreg (OCF.Denis.C_seed s _ _ _
      (OCF.Denis.diagonalIter_lt_succ s r hreg hlarge hindex n))

theorem diagonal_dense (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) (hreg : OCF.Denis.RegularIndex s r) (hlarge : OCF.Denis.I s 0 0 < r)
    (hindex : ∀ a b, 0 < a → OCF.Denis.C s a b r) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) r) := by
  apply dense_of_normal_sequence s _ _ (OCF.Denis.diagonal_fundamentalSequence s r hreg hlarge hindex)
  intro n
  exact represented_psi_of_mem s _ _ ⟨omega1, omega1_isNormal s, rfl⟩
    (diagonalIter_represented s r hr hreg hlarge hindex n) (Or.inl ⟨0, rfl⟩)
    (OCF.Denis.diagonalIter_argument_normal s r hreg hlarge hindex n)

theorem finite_parameters_diagonal_dense (s : OCF.Denis.Supply) (n m : Nat) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0)
      (OCF.Denis.I s (OCF.Denis.finite n) (OCF.Denis.finite m))) := by
  by_cases h : 0 < n + m
  · exact diagonal_dense s _
      (represented_I s _ _ (finite_represented s n) (finite_represented s m))
      (OCF.Denis.finite_parameters_regular s n m) (OCF.Denis.first_lt_finite_parameters s n m h)
      (OCF.Denis.finite_parameters_mem_C s n m)
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n
    subst m
    exact epsilon_dense s

theorem revised_finite_parameters_diagonal_fundamentalSequence (s : OCF.Denis.Supply)
    (n m : Nat) :
    OCF.Denis.FundamentalSequence
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s (OCF.Denis.finite n) (OCF.Denis.finite m)))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0)
        (OCF.Denis.I s (OCF.Denis.finite n) (OCF.Denis.finite m)))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (finite_parameters_diagonal_dense s n m)

end
end T.Correspondence.Denis.Covering
