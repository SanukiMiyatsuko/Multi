import Multi.term3.Term3Correspondence
import Multi.term3.Denis.DiagonalSequence

/-! Connections to the actual ordinal-valued closure construction.
Only the supported direct reading is interpreted here. No general
order-embedding theorem or inaccessible-collapse correspondence is assumed.
-/

namespace T.Correspondence

open OCF.Ordinal

noncomputable section

def Denis.denote (s : OCF.Denis.Supply) : Denis.Term → OCF.Denis.O
  | .zero => 0
  | .add a b => Denis.denote s a + Denis.denote s b
  | .I a b => OCF.Denis.I s (Denis.denote s a) (Denis.denote s b)
  | .psi k a => OCF.Denis.psi s (Denis.denote s k) (Denis.denote s a)

def readOrdinal (s : OCF.Denis.Supply) (t : T) : Option OCF.Denis.O :=
  (direct t).map (Denis.denote s)

theorem Denis.denote_one (s : OCF.Denis.Supply) : Denis.denote s Denis.one = succ 0 :=
  OCF.Denis.psi_first_zero s

theorem Denis.denote_omega (s : OCF.Denis.Supply) :
    Denis.denote s (Denis.exp Denis.one) = OCF.Denis.omega := by
  change OCF.Denis.psi s (OCF.Denis.I s 0 0) (Denis.denote s Denis.one) = _
  rw [Denis.denote_one, OCF.Denis.psi_first_one]

theorem Denis.denote_I1 (s : OCF.Denis.Supply) :
    Denis.denote s Denis.I1 = OCF.Denis.I s (succ 0) 0 := by
  change OCF.Denis.I s (Denis.denote s Denis.one) 0 = _
  rw [Denis.denote_one]

theorem read_zero (s : OCF.Denis.Supply) : readOrdinal s Z = some 0 := rfl

theorem read_one (s : OCF.Denis.Supply) : readOrdinal s one = some (succ 0) := by
  change some (Denis.denote s Denis.one) = _
  rw [Denis.denote_one]

theorem read_omega (s : OCF.Denis.Supply) :
    readOrdinal s (exp one) = some OCF.Denis.omega := by
  change some (Denis.denote s (Denis.exp Denis.one)) = _
  rw [Denis.denote_omega]

theorem read_exp_omega (s : OCF.Denis.Supply) :
    readOrdinal s (exp (exp one)) =
      some (OCF.Denis.psi s (OCF.Denis.I s 0 0) OCF.Denis.omega) := by
  change some (OCF.Denis.psi s (OCF.Denis.I s 0 0)
    (Denis.denote s (Denis.exp Denis.one))) = _
  rw [Denis.denote_omega]

theorem read_uncountable (s : OCF.Denis.Supply) :
    readOrdinal s uncountable = some (OCF.Denis.I s 0 0) := rfl

theorem read_inaccessible (s : OCF.Denis.Supply) :
    readOrdinal s inaccessible = some (OCF.Denis.I s (succ 0) 0) := by
  change some (OCF.Denis.I s (Denis.denote s Denis.one) 0) = _
  rw [Denis.denote_one]

theorem read_epsilon (s : OCF.Denis.Supply) :
    readOrdinal s epsilon =
      some (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0)) := rfl

theorem read_collapseI (s : OCF.Denis.Supply) :
    readOrdinal s collapseI =
      some (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s (succ 0) 0)) := by
  change some (OCF.Denis.psi s (OCF.Denis.I s 0 0)
    (OCF.Denis.I s (Denis.denote s Denis.one) 0)) = _
  rw [Denis.denote_one]

theorem read_ofNat (s : OCF.Denis.Supply) (n : Nat) :
    readOrdinal s (T.ofNat n) = some (OCF.Denis.finite n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => exact read_one s
    | succ n =>
      unfold readOrdinal
      change (direct (P Z Z Z (T.ofNat (n + 1)))).map (Denis.denote s) = _
      rw [direct_one_tail _ (show T.ofNat (n + 1) ≠ Z from T.noConfusion)]
      have hone := Denis.denote_one s
      cases hd : direct (T.ofNat (n + 1)) with
      | none =>
        change (direct (T.ofNat (n + 1))).map (Denis.denote s) = _ at ih
        rw [hd] at ih
        cases ih
      | some t =>
        change (direct (T.ofNat (n + 1))).map (Denis.denote s) = _ at ih
        rw [hd] at ih
        have ht : Denis.denote s t = OCF.Denis.finite (n + 1) := Option.some.inj ih
        change some (Denis.denote s Denis.one + Denis.denote s t) = _
        rw [hone, ht]
        change some (OCF.Denis.finite 1 + OCF.Denis.finite (n + 1)) = _
        rw [OCF.Denis.finite_add, Nat.add_comm 1 (n + 1)]

theorem read_fund_ofNat_succ (s : OCF.Denis.Supply) (n m : Nat) :
    readOrdinal s (T.fund (T.ofNat (n + 1)) (T.ofNat m)) =
      some (OCF.Denis.finite n) := by
  rw [fund_ofNat_succ, read_ofNat]

/-- Actual ordinal compatibility of the fundamental sequence at omega. -/
theorem read_fund_omega (s : OCF.Denis.Supply) (n : Nat) :
    readOrdinal s (T.fund (exp one) (T.ofNat n)) = some (OCF.Denis.finite n) := by
  rw [fund_omega, read_ofNat]

theorem omega_sequence_cofinal :
    OCF.Ordinal.sup OCF.Denis.finite = OCF.Denis.omega := rfl

theorem omega_sequence_strict (n : Nat) :
    OCF.Denis.finite n < OCF.Denis.finite (n + 1) := lt_succ_self _

theorem epsilon_sequence_shift_ordinal (s : OCF.Denis.Supply) (n : Nat) :
    readOrdinal s (T.fund epsilon (T.ofNat (n + 1))) =
      some (Denis.denote s (Denis.epsilonSeq n)) := by
  unfold readOrdinal
  rw [epsilon_sequence_shift]
  rfl

theorem Denis.denote_iterate_exp (s : OCF.Denis.Supply) (n : Nat) :
    Denis.denote s (Denis.iterate Denis.exp .zero n) = OCF.Denis.tower s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change OCF.Denis.psi s (OCF.Denis.I s 0 0)
      (Denis.denote s (Denis.iterate Denis.exp .zero n)) = _
    rw [ih]
    rfl

theorem read_fund_epsilon (s : OCF.Denis.Supply) (n : Nat) :
    readOrdinal s (T.fund epsilon (T.ofNat n)) = some (OCF.Denis.tower s (n + 1)) := by
  rw [fund_epsilon]
  unfold readOrdinal
  rw [direct_exp_tower]
  exact congrArg some (Denis.denote_iterate_exp s (n + 1))

/-- Both compatibility and the semantic fundamental-sequence properties. -/
theorem epsilon_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0))
      (fun n => OCF.Denis.tower s (n + 1)) :=
  OCF.Denis.tower_fundamentalSequence s 1

theorem Denis.epsilonSeq_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (Denis.denote s Denis.epsilon)
      (fun n => Denis.denote s (Denis.epsilonSeq n)) := by
  have heq : (fun n => Denis.denote s (Denis.epsilonSeq n)) =
      (fun n => OCF.Denis.tower s (n + 2)) := by
    funext n
    have h := epsilon_sequence_shift_ordinal s n
    rw [read_fund_epsilon] at h
    exact (Option.some.inj h).symm
  rw [heq]
  exact OCF.Denis.tower_fundamentalSequence s 2

theorem Denis.denote_iterate_collapseI (s : OCF.Denis.Supply) (n : Nat) :
    Denis.denote s (Denis.iterate (.psi Denis.I1) Denis.one n) =
      OCF.Denis.diagonalIter s (OCF.Denis.I s (succ 0) 0) n := by
  induction n with
  | zero => exact Denis.denote_one s
  | succ n ih =>
    change OCF.Denis.psi s (Denis.denote s Denis.I1)
      (Denis.denote s (Denis.iterate (.psi Denis.I1) Denis.one n)) = _
    rw [Denis.denote_I1, ih]
    rfl

theorem Denis.denote_collapseISeq (s : OCF.Denis.Supply) (n : Nat) :
    Denis.denote s (Denis.collapseISeq n) =
      OCF.Denis.diagonalSeq s (OCF.Denis.I s (succ 0) 0) n := by
  change OCF.Denis.psi s (OCF.Denis.I s 0 0)
    (Denis.denote s (Denis.iterate (.psi Denis.I1) Denis.one n)) = _
  rw [Denis.denote_iterate_collapseI]
  rfl

theorem Denis.collapseISeq_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (Denis.denote s Denis.collapseI)
      (fun n => Denis.denote s (Denis.collapseISeq n)) := by
  have heq : (fun n => Denis.denote s (Denis.collapseISeq n)) =
      OCF.Denis.diagonalSeq s (OCF.Denis.I s (succ 0) 0) :=
    funext (Denis.denote_collapseISeq s)
  rw [heq]
  change OCF.Denis.FundamentalSequence
    (OCF.Denis.psi s (OCF.Denis.I s 0 0) (Denis.denote s Denis.I1)) _
  rw [Denis.denote_I1]
  exact OCF.Denis.inaccessible_diagonal_fundamentalSequence s

/-- Unlike a raw-syntax inequality, this difference is witnessed on ordinals. -/
theorem collapseI_sequence_zero_ne_ordinal (s : OCF.Denis.Supply) :
    readOrdinal s (T.fund collapseI (T.ofNat 0)) ≠
      some (Denis.denote s (Denis.collapseISeq 0)) := by
  rw [fund_collapseI]
  change readOrdinal s one ≠ some (Denis.denote s (Denis.exp Denis.one))
  rw [read_one, Denis.denote_omega]
  intro h
  have heq := Option.some.inj h
  exact OCF.Ordinal.lt_irrefl OCF.Denis.omega
    (heq ▸ OCF.Denis.finite_lt_omega 1)

end
end T.Correspondence
