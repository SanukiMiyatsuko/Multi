import Multi.term2.OCF.Arithmetic

/-! Ordinal (rather than syntactic) definitions used by Denis's OCF.
No inaccessible-cardinal existence axiom is declared. `Supply` records the
large-cardinal hypothesis needed to enumerate all the requested ranks.
-/

namespace OCF.Denis

open Ordinal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev O := Ordinal.{0}

def finite : Nat → O
  | 0 => 0
  | n + 1 => succ (finite n)

/-- The ordinal omega, the supremum of the finite ordinals. -/
def omega : O := sup finite

theorem finite_add (n m : Nat) : finite n + finite m = finite (n + m) := by
  induction m with
  | zero => exact add_zero _
  | succ m ih =>
    change finite n + succ (finite m) = succ (finite (n + m))
    rw [add_succ, ih]

theorem lt_finite_iff (x : O) (n : Nat) : x < finite n ↔ ∃ m, m < n ∧ x = finite m := by
  induction n with
  | zero => exact ⟨fun h => False.elim (not_lt_zero x h),
      fun ⟨_, h, _⟩ => False.elim (Nat.not_lt_zero _ h)⟩
  | succ n ih =>
    change x < succ (finite n) ↔ _
    rw [lt_succ_iff_le]
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨m, hm, hx⟩ := ih.mp h
        exact ⟨m, Nat.lt_trans hm (Nat.lt_succ_self n), hx⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨m, hm, rfl⟩
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with
      | inl hm => exact Or.inl (ih.mpr ⟨m, hm, rfl⟩)
      | inr hm => exact Or.inr (congrArg finite hm)

theorem lt_omega_iff (x : O) : x < omega ↔ ∃ n, x = finite n := by
  rw [omega, lt_sup_iff]
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨m, _, hm⟩ := (lt_finite_iff x n).mp h
    exact ⟨m, hm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, lt_succ_self (finite n)⟩

theorem finite_lt_omega (n : Nat) : finite n < omega :=
  (lt_omega_iff _).mpr ⟨n, rfl⟩

theorem omega_add_closed {x y : O} (hx : x < omega) (hy : y < omega) : x + y < omega := by
  obtain ⟨n, rfl⟩ := (lt_omega_iff x).mp hx
  obtain ⟨m, rfl⟩ := (lt_omega_iff y).mp hy
  rw [finite_add]
  exact finite_lt_omega _

/-- Every sequence of length below kappa is strictly bounded in kappa.
For kappa > omega this is the regular-cardinal condition. -/
def UncountableRegular (kappa : O) : Prop :=
  omega < kappa ∧ ∀ (b : O), b < kappa →
    ∀ f : (representative b).Carrier → O,
      (∀ i, f i < kappa) → ∃ bound, bound < kappa ∧ ∀ i, f i < bound

def Inaccessible : O → O → Prop :=
  lt_wellFounded.fix (fun rank previous kappa =>
    UncountableRegular kappa ∧
      ∀ r, ∀ hr : r < rank, ∀ x, x < kappa →
        ∃ y, x < y ∧ y < kappa ∧ previous r hr y)

theorem inaccessible_iff (rank kappa : O) :
    Inaccessible rank kappa ↔ UncountableRegular kappa ∧
      ∀ r, r < rank → ∀ x, x < kappa →
        ∃ y, x < y ∧ y < kappa ∧ Inaccessible r y := by
  unfold Inaccessible
  rw [WellFounded.fix_eq]

theorem inaccessible_zero_iff (kappa : O) :
    Inaccessible 0 kappa ↔ UncountableRegular kappa := by
  rw [inaccessible_iff]
  exact ⟨And.left, fun h => ⟨h, fun r hr => False.elim (not_lt_zero r hr)⟩⟩

theorem inaccessible_regular {rank kappa : O} (h : Inaccessible rank kappa) :
    UncountableRegular kappa := ((inaccessible_iff rank kappa).mp h).1

/-- An explicit mathematical hypothesis, not a new Lean axiom. -/
structure Supply : Prop where
  unbounded : ∀ rank lower : O, ∃ kappa, lower < kappa ∧ Inaccessible rank kappa

noncomputable def least (P : O → Prop) (h : ∃ a, P a) : O :=
  Classical.choose (Ordinal.exists_min P h)

theorem least_spec (P : O → Prop) (h : ∃ a, P a) :
    P (least P h) ∧ ∀ b, b < least P h → ¬ P b :=
  Classical.choose_spec (Ordinal.exists_min P h)

theorem least_le (P : O → Prop) (h : ∃ a, P a) {b : O} (hb : P b) :
    least P h ≤ b :=
  (not_lt_iff_le b (least P h)).mp (fun hlt => (least_spec P h).2 b hlt hb)

noncomputable def first (s : Supply) (rank : O) : O :=
  least (Inaccessible rank) (by
    obtain ⟨k, _, hk⟩ := s.unbounded rank 0
    exact ⟨k, hk⟩)

noncomputable def next (s : Supply) (rank lower : O) : O :=
  least (fun k => lower < k ∧ Inaccessible rank k) (s.unbounded rank lower)

theorem first_spec (s : Supply) (rank : O) : Inaccessible rank (first s rank) :=
  (least_spec _ _).1

theorem first_le (s : Supply) (rank k : O) (hk : Inaccessible rank k) :
    first s rank ≤ k := least_le _ _ hk

theorem next_spec (s : Supply) (rank lower : O) :
    lower < next s rank lower ∧ Inaccessible rank (next s rank lower) :=
  (least_spec (fun k => lower < k ∧ Inaccessible rank k) (s.unbounded rank lower)).1

noncomputable def I (s : Supply) (rank : O) : O → O :=
  lt_wellFounded.fix (fun b previous =>
    if b = 0 then first s rank
    else if hb : ∃ c, b = succ c then
      let c := Classical.choose hb
      have hc : c < b := by rw [Classical.choose_spec hb]; exact lt_succ_self c
      next s rank (previous c hc)
    else sup (fun x : (representative b).Carrier =>
      previous (type ((representative b).below x)) (initial_lt b x)))

theorem I_eq (s : Supply) (rank b : O) :
    I s rank b =
      if b = 0 then first s rank
      else if hb : ∃ c, b = succ c then
        next s rank (I s rank (Classical.choose hb))
      else sup (fun x : (representative b).Carrier =>
        I s rank (type ((representative b).below x))) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem I_zero (s : Supply) (rank : O) : I s rank 0 = first s rank := by
  rw [I_eq, ite_eq_left rfl]

theorem succ_injective {a b : O} (h : succ a = succ b) : a = b := by
  apply le_antisymm
  · apply (lt_succ_iff_le a b).mp
    rw [← h]
    exact lt_succ_self a
  · apply (lt_succ_iff_le b a).mp
    rw [h]
    exact lt_succ_self b

theorem I_succ (s : Supply) (rank b : O) :
    I s rank (succ b) = next s rank (I s rank b) := by
  have hne : succ b ≠ 0 := by
    intro h
    exact not_lt_zero b (h ▸ lt_succ_self b)
  rw [I_eq, ite_eq_right hne, dite_eq_left (show ∃ c, succ b = succ c from ⟨b, rfl⟩)]
  congr 2
  exact (succ_injective (Classical.choose_spec (show ∃ c, succ b = succ c from ⟨b, rfl⟩))).symm

theorem I_limit (s : Supply) (rank b : O) (hzero : b ≠ 0)
    (hsucc : ¬ ∃ c, b = succ c) :
    I s rank b = sup (fun x : (representative b).Carrier =>
      I s rank (type ((representative b).below x))) := by
  rw [I_eq, ite_eq_right hzero, dite_eq_right hsucc]

/-- The allowed regular indices in the cited definition. -/
def RegularIndex (s : Supply) (k : O) : Prop :=
  (∃ a, k = I s a 0) ∨ ∃ a b, k = I s a (succ b)

theorem regularIndex_regular (s : Supply) (k : O) (h : RegularIndex s k) :
    UncountableRegular k := by
  rcases h with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · rw [I_zero]; exact inaccessible_regular (first_spec s a)
  · rw [I_succ]; exact inaccessible_regular (next_spec s a (I s a b)).2

end
end OCF.Denis
