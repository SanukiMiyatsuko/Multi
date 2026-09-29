import Multi.term3.Term3Denis

/-! The source's semantic normal-form conditions on the raw notation.
In particular the argument-membership condition is proved, not included
as an assumption in the correspondence theorems below. -/

namespace T.Correspondence
open OCF.Ordinal
noncomputable section

def Denis.Term.isPrincipal : Denis.Term → Prop
  | .I _ _ | .psi _ _ => True
  | _ => False

def Denis.Term.leading : Denis.Term → Denis.Term
  | .add a _ => a.leading
  | a => a

/-- Binary, right-associated version of the source's normal form.
The sum condition orders its principal summands; I and psi have the
source's argument restrictions on their actual ordinal denotations. -/
inductive Denis.IsNormal (s : OCF.Denis.Supply) : Denis.Term → Prop where
  | zero : IsNormal s .zero
  | index {r b : Denis.Term} : IsNormal s r → IsNormal s b →
      denote s r < OCF.Denis.I s (denote s r) (denote s b) →
      denote s b < OCF.Denis.I s (denote s r) (denote s b) → IsNormal s (.I r b)
  | collapse {k a : Denis.Term} : IsNormal s k → IsNormal s a →
      OCF.Denis.RegularIndex s (denote s k) →
      OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a))
        (denote s a) → IsNormal s (.psi k a)
  | sum {a b : Denis.Term} : IsNormal s a → IsNormal s b → a.isPrincipal →
      AddPrincipal (denote s a) → 0 < denote s b →
      denote s b.leading ≤ denote s a → IsNormal s (.add a b)

theorem Denis.omega1_isNormal (s : OCF.Denis.Supply) : Denis.IsNormal s Denis.omega1 :=
  .index .zero .zero (OCF.Denis.regular_pos (OCF.Denis.first_regular s))
    (OCF.Denis.regular_pos (OCF.Denis.first_regular s))

theorem Denis.tower_isNormal (s : OCF.Denis.Supply) (n : Nat) :
    Denis.IsNormal s (Denis.iterate Denis.exp .zero n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    apply Denis.IsNormal.collapse (Denis.omega1_isNormal s) ih (Or.inl ⟨0, rfl⟩)
    rw [Denis.denote_iterate_exp]
    exact OCF.Denis.tower_argument_normal s n

theorem Denis.epsilon_isNormal (s : OCF.Denis.Supply) : Denis.IsNormal s Denis.epsilon :=
  .collapse (Denis.omega1_isNormal s) (Denis.omega1_isNormal s) (Or.inl ⟨0, rfl⟩)
    (OCF.Denis.first_diagonal_argument_normal s)

theorem Denis.epsilonSeq_isNormal (s : OCF.Denis.Supply) (n : Nat) :
    Denis.IsNormal s (Denis.epsilonSeq n) := by
  have h := Denis.tower_isNormal s (n + 2)
  change Denis.IsNormal s (Denis.exp (Denis.iterate Denis.exp .zero (n + 1))) at h
  rw [denis_exp_tower_shift] at h
  exact h

theorem epsilon_fund_read_normal (s : OCF.Denis.Supply) (n : Nat) :
    ∃ t, direct (T.fund epsilon (T.ofNat n)) = some t ∧ Denis.IsNormal s t := by
  rw [fund_epsilon, direct_exp_tower]
  exact ⟨_, rfl, Denis.tower_isNormal s (n + 1)⟩

theorem Denis.one_isNormal (s : OCF.Denis.Supply) : Denis.IsNormal s Denis.one :=
  Denis.tower_isNormal s 1

theorem Denis.I1_isNormal (s : OCF.Denis.Supply) : Denis.IsNormal s Denis.I1 := by
  apply Denis.IsNormal.index (Denis.one_isNormal s) .zero
  · rw [Denis.denote_one]
    exact OCF.Ordinal.lt_trans _ _ _
      (OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.finite_lt_omega 1) (OCF.Denis.first_regular s).1)
      (OCF.Denis.first_lt_first_inaccessible s)
  · rw [Denis.denote_one]
    exact OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ 0, rfl⟩))

theorem Denis.iterate_collapseI_isNormal (s : OCF.Denis.Supply) (n : Nat) :
    Denis.IsNormal s (Denis.iterate (.psi Denis.I1) Denis.one n) := by
  induction n with
  | zero => exact Denis.one_isNormal s
  | succ n ih =>
    apply Denis.IsNormal.collapse (Denis.I1_isNormal s) ih
    · rw [Denis.denote_I1]
      exact Or.inl ⟨succ 0, rfl⟩
    · rw [Denis.denote_I1, Denis.denote_iterate_collapseI]
      apply OCF.Denis.C_seed
      exact OCF.Denis.diagonalIter_lt_succ s _ (Or.inl ⟨succ 0, rfl⟩)
        (OCF.Denis.first_lt_first_inaccessible s) (OCF.Denis.first_inaccessible_mem_C s) n

theorem Denis.collapseISeq_isNormal (s : OCF.Denis.Supply) (n : Nat) :
    Denis.IsNormal s (Denis.collapseISeq n) := by
  apply Denis.IsNormal.collapse (Denis.omega1_isNormal s)
    (Denis.iterate_collapseI_isNormal s n) (Or.inl ⟨0, rfl⟩)
  rw [Denis.denote_iterate_collapseI]
  exact OCF.Denis.diagonalIter_argument_normal s _ (Or.inl ⟨succ 0, rfl⟩)
    (OCF.Denis.first_lt_first_inaccessible s) (OCF.Denis.first_inaccessible_mem_C s) n

theorem Denis.collapseI_isNormal (s : OCF.Denis.Supply) :
    Denis.IsNormal s Denis.collapseI := by
  apply Denis.IsNormal.collapse (Denis.omega1_isNormal s) (Denis.I1_isNormal s)
    (Or.inl ⟨0, rfl⟩)
  rw [Denis.denote_I1]
  exact OCF.Denis.first_inaccessible_mem_C s _ _
    (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ 0, rfl⟩)))

end
end T.Correspondence
