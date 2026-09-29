import Multi.term3.Denis.Covering

/-! A uniform replacement expansion on all represented normal ordinals.
Successors in that ordered set use their predecessor; limits use a strict
subsequence of the exhaustive finite-prefix maxima. Actual ordinal
cofinality is stated separately from cofinality among normal values.
-/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def HasPredecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  ∃ b, Represented s b ∧ b < a ∧ ∀ c, Represented s c → c < a → c ≤ b

def NormalLimit (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  0 < a ∧ ∀ b, Represented s b → b < a →
    ∃ c, Represented s c ∧ b < c ∧ c < a

theorem normalLimit_of_no_predecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : 0 < a) (hp : ¬ HasPredecessor s a) : NormalLimit s a := by
  refine ⟨ha, ?_⟩
  intro b hb hba
  by_cases h : ∃ c, Represented s c ∧ b < c ∧ c < a
  · exact h
  · apply False.elim
    apply hp
    refine ⟨b, hb, hba, ?_⟩
    intro c hc hca
    apply (not_lt_iff_le _ _).mp
    intro hbc
    exact h ⟨c, hc, hbc, hca⟩

theorem normalLimit_no_predecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) : ¬ HasPredecessor s a := by
  rintro ⟨b, hb, hba, hmax⟩
  obtain ⟨c, hc, hbc, hca⟩ := ha.2 b hb hba
  exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hbc (hmax c hc hca))

theorem advance_exists (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) (i : Nat) : ∃ j, i < j ∧ value s a i < value s a j := by
  obtain ⟨b, hb, hbi, hba⟩ := ha.2 _ (value_represented s a i) (value_lt s a ha.1 i)
  obtain ⟨j, hj⟩ := value_covers s a b hb hba
  refine ⟨max j (i + 1), by omega, ?_⟩
  exact OCF.Ordinal.lt_of_lt_of_le hbi
    (OCF.Ordinal.le_trans hj (value_mono s a (Nat.le_max_left _ _)))

def naturalWellOrder : OCF.WellOrder where
  Carrier := Nat
  lt := (· < ·)
  irrefl := Nat.lt_irrefl
  trans _ _ _ := Nat.lt_trans
  total := Nat.lt_trichotomy
  wellFounded := Nat.lt_wfRel.wf

def advance (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a) (i : Nat) : Nat :=
  Classical.choose (OCF.WellOrder.exists_min naturalWellOrder
    (fun j => i < j ∧ value s a i < value s a j) (advance_exists s a ha i))

theorem advance_spec (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a) (i : Nat) :
    i < advance s a ha i ∧ value s a i < value s a (advance s a ha i) :=
  (Classical.choose_spec (OCF.WellOrder.exists_min naturalWellOrder
    (fun j => i < j ∧ value s a i < value s a j) (advance_exists s a ha i))).1

theorem advance_minimal (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a)
    (i j : Nat) (hij : i < j) (hv : value s a i < value s a j) : advance s a ha i ≤ j := by
  have h := (Classical.choose_spec (OCF.WellOrder.exists_min naturalWellOrder
    (fun j => i < j ∧ value s a i < value s a j) (advance_exists s a ha i))).2
  apply Nat.le_of_not_gt
  intro hj
  exact h j hj ⟨hij, hv⟩

def strictIndex (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a) : Nat → Nat
  | 0 => 0
  | n + 1 => advance s a ha (strictIndex s a ha n)

theorem le_strictIndex (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a) (n : Nat) :
    n ≤ strictIndex s a ha n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := (advance_spec s a ha (strictIndex s a ha n)).1
    change n + 1 ≤ advance s a ha (strictIndex s a ha n)
    omega

def strictValue (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : NormalLimit s a) (n : Nat) : OCF.Denis.O :=
  value s a (strictIndex s a ha n)

theorem strictValue_lt_succ (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) (n : Nat) : strictValue s a ha n < strictValue s a ha (n + 1) :=
  (advance_spec s a ha (strictIndex s a ha n)).2

theorem strictValue_strict (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) {n m : Nat} (h : n < m) : strictValue s a ha n < strictValue s a ha m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact OCF.Ordinal.lt_trans _ _ _ (ih h) (strictValue_lt_succ s a ha m)
    · exact strictValue_lt_succ s a ha n

theorem strictValue_covers (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (ha : NormalLimit s a) (hb : Represented s b) (hba : b < a) :
    ∃ n, b < strictValue s a ha n := by
  obtain ⟨c, hc, hbc, hca⟩ := ha.2 b hb hba
  obtain ⟨n, hn⟩ := value_covers s a c hc hca
  exact ⟨n, OCF.Ordinal.lt_of_lt_of_le hbc
    (OCF.Ordinal.le_trans hn (value_mono s a (le_strictIndex s a ha n)))⟩

def predecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O) (h : HasPredecessor s a) : OCF.Denis.O :=
  Classical.choose h

theorem predecessor_spec (s : OCF.Denis.Supply) (a : OCF.Denis.O) (h : HasPredecessor s a) :
    Represented s (predecessor s a h) ∧ predecessor s a h < a ∧
      ∀ c, Represented s c → c < a → c ≤ predecessor s a h := Classical.choose_spec h

def revisedValue (s : OCF.Denis.Supply) (a : OCF.Denis.O) (n : Nat) : OCF.Denis.O :=
  if hz : a = 0 then 0
  else if hp : HasPredecessor s a then predecessor s a hp
  else strictValue s a (normalLimit_of_no_predecessor s a ((zero_lt_iff_ne_zero a).mpr hz) hp) n

theorem revisedValue_zero (s : OCF.Denis.Supply) (n : Nat) : revisedValue s 0 n = 0 := by
  simp [revisedValue]

theorem revisedValue_predecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hp : HasPredecessor s a) (n : Nat) : revisedValue s a n = predecessor s a hp := by
  have hz : a ≠ 0 := (zero_lt_iff_ne_zero a).mp
    (OCF.Ordinal.lt_of_le_of_lt (zero_le _) (predecessor_spec s a hp).2.1)
  simp [revisedValue, hz, hp]

theorem revisedValue_limit (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) (n : Nat) : revisedValue s a n = strictValue s a ha n := by
  have hz := (zero_lt_iff_ne_zero a).mp ha.1
  have hp := normalLimit_no_predecessor s a ha
  simp [revisedValue, hz, hp]

theorem revisedValue_represented (s : OCF.Denis.Supply) (a : OCF.Denis.O) (n : Nat) :
    Represented s (revisedValue s a n) := by
  unfold revisedValue
  split
  · exact represented_zero s
  · split
    · exact (predecessor_spec s a _).1
    · exact value_represented s a _

theorem revisedValue_lt (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : 0 < a) (n : Nat) :
    revisedValue s a n < a := by
  unfold revisedValue
  split
  · exact ha
  · split
    · exact (predecessor_spec s a _).2.1
    · exact value_lt s a ha _

theorem revisedValue_le (s : OCF.Denis.Supply) (a : OCF.Denis.O) (n : Nat) :
    revisedValue s a n ≤ a := by
  by_cases hz : a = 0
  · rw [hz, revisedValue_zero]; exact le_refl _
  · exact Or.inl (revisedValue_lt s a ((zero_lt_iff_ne_zero a).mpr hz) n)

theorem revisedValue_covers (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (hb : Represented s b) (hba : b < a) : ∃ n, b ≤ revisedValue s a n := by
  have ha : 0 < a := OCF.Ordinal.lt_of_le_of_lt (zero_le b) hba
  by_cases hp : HasPredecessor s a
  · refine ⟨0, ?_⟩
    rw [revisedValue_predecessor s a hp]
    exact (predecessor_spec s a hp).2.2 b hb hba
  · have hl := normalLimit_of_no_predecessor s a ha hp
    obtain ⟨n, hn⟩ := strictValue_covers s a b hl hb hba
    exact ⟨n, Or.inl (by rw [revisedValue_limit s a hl]; exact hn)⟩

def revisedStep (s : OCF.Denis.Supply) (a : NormalOrdinal s) (n : Nat) : NormalOrdinal s :=
  ⟨revisedValue s a.1 n, revisedValue_represented s a.1 n⟩

def follow (s : OCF.Denis.Supply) (a : NormalOrdinal s) : List Nat → NormalOrdinal s
  | [] => a
  | n :: ns => follow s (revisedStep s a n) ns

theorem follow_le (s : OCF.Denis.Supply) (a : NormalOrdinal s) (ns : List Nat) :
    (follow s a ns).1 ≤ a.1 := by
  induction ns generalizing a with
  | nil => exact le_refl _
  | cons n ns ih => exact OCF.Ordinal.le_trans (ih (revisedStep s a n)) (revisedValue_le s a.1 n)

theorem follow_exists_of_lt (s : OCF.Denis.Supply) (a b : NormalOrdinal s) (hba : b.1 < a.1) :
    ∃ ns, follow s a ns = b := by
  induction a using (normalOrdinalWellOrder s).wellFounded.induction with
  | h a ih =>
    obtain ⟨n, hn⟩ := revisedValue_covers s a.1 b.1 b.2 hba
    have ha : 0 < a.1 := OCF.Ordinal.lt_of_le_of_lt (zero_le b.1) hba
    rcases hn with h | h
    · obtain ⟨ns, hns⟩ := ih (revisedStep s a n) (revisedValue_lt s a.1 ha n) h
      exact ⟨n :: ns, hns⟩
    · exact ⟨[n], Subtype.ext h.symm⟩

/-- Exactly all smaller or equal represented normal ordinals are reached. -/
theorem follow_exists_iff_le (s : OCF.Denis.Supply) (a b : NormalOrdinal s) :
    (∃ ns, follow s a ns = b) ↔ b.1 ≤ a.1 := by
  constructor
  · rintro ⟨ns, rfl⟩
    exact follow_le s a ns
  · intro h
    rcases h with h | h
    · exact follow_exists_of_lt s a b h
    · exact ⟨[], Subtype.ext h.symm⟩

/-- The upgrade to cofinality in the original ordinal semantics is explicit. -/
theorem revised_fundamentalSequence_of_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : 0 < a) (hd : DenseBelow s a) : OCF.Denis.FundamentalSequence a (revisedValue s a) := by
  have hl : NormalLimit s a := ⟨ha, fun b _ hb => hd b hb⟩
  refine ⟨revisedValue_lt s a ha, ?_, ?_⟩
  · intro n m h
    rw [revisedValue_limit s a hl n, revisedValue_limit s a hl m]
    exact strictValue_strict s a hl h
  · intro x hx
    obtain ⟨b, hb, hxb, hba⟩ := hd x hx
    obtain ⟨n, hn⟩ := revisedValue_covers s a b hb hba
    exact ⟨n, OCF.Ordinal.lt_of_lt_of_le hxb hn⟩

end
end T.Correspondence.Denis.Covering
