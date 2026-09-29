import Multi.term3.Denis.WellDefined

/-! Semantic fundamental sequences. The predicates below require strict
increase, descent, and cofinality in actual ordinals, not merely equations
between notation trees. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def IsLimit (a : O) : Prop := a ≠ 0 ∧ ¬ ∃ b, a = succ b

theorem regular_succ_lt {k a : O} (hk : UncountableRegular k) (ha : a < k) :
    succ a < k := by
  obtain ⟨b, hb, hab⟩ := small_unit hk (fun _ => a) (fun _ => ha)
  exact lt_of_le_of_lt ((succ_le_iff_lt a b).mpr (hab ())) hb

theorem regular_add_closed {k : O} (hk : UncountableRegular k)
    {a b : O} (ha : a < k) (hb : b < k) : a + b < k := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    let f : (representative b).Carrier → O := fun x =>
      succ (a + type ((representative b).below x))
    have hf : ∀ x, f x < k := fun x => regular_succ_lt hk
      (ih _ (initial_lt b x) (lt_trans _ _ _ (initial_lt b x) hb))
    obtain ⟨c, hc, hfc⟩ := small_representative hk b hb f hf
    have hbound (d : O) (had : a ≤ d) (hcd : c ≤ d) : a + b ≤ d := by
      rw [add_eq]
      apply (sup_le_iff _ d).mpr
      intro x
      cases x with
      | none => exact had
      | some x => exact le_trans (Or.inl (hfc x)) hcd
    rcases lt_total a c with h | h | h
    · exact lt_of_le_of_lt (hbound c (Or.inl h) (le_refl c)) hc
    · exact lt_of_le_of_lt (hbound c (Or.inr h) (le_refl c)) hc
    · exact lt_of_le_of_lt (hbound a (le_refl a) (Or.inl h)) ha

theorem psi_addPrincipal (s : Supply) (k a : O) (hk : UncountableRegular k) :
    AddPrincipal (psi s k a) := by
  intro x y hx hy
  exact psi_closed s k a (x + y)
    (C_add s a _ x y (C_seed s a _ x hx) (C_seed s a _ y hy))
    (regular_add_closed hk (lt_trans _ _ _ hx (psi_lt s k a hk))
      (lt_trans _ _ _ hy (psi_lt s k a hk)))

/-- Ordinal-indexed version for the uncountable rules. -/
structure TransfiniteFundamentalSequence (a length : O) (f : O → O) : Prop where
  below : ∀ i, i < length → f i < a
  strict : ∀ i j, i < j → j < length → f i < f j
  cofinal : ∀ x, x < a → ∃ i, i < length ∧ x < f i

theorem regular_fundamentalSequence (k : O) (hk : UncountableRegular k) :
    TransfiniteFundamentalSequence k k (fun i => i) :=
  ⟨fun _ hi => hi, fun _ _ hij _ => hij,
    fun x hx => ⟨succ x, regular_succ_lt hk hx, lt_succ_self x⟩⟩

/-- No shorter ordinal-indexed sequence can be cofinal in a regular index. -/
theorem regular_no_shorter_cofinal (k : O) (hk : UncountableRegular k)
    (b : O) (hb : b < k) (f : O → O) (hf : ∀ i, i < b → f i < k) :
    ¬ ∀ x, x < k → ∃ i, i < b ∧ x < f i := by
  obtain ⟨bound, hbound, hfb⟩ := hk.2 b hb
    (fun i => f (type ((representative b).below i))) (fun i => hf _ (initial_lt b i))
  intro hcofinal
  obtain ⟨i, hi, hbi⟩ := hcofinal bound hbound
  obtain ⟨j, hj⟩ := initial_surjective b i hi
  have hh := hfb j
  rw [← hj] at hh
  exact lt_asymm hbi hh

theorem succ_lt_limit {a b : O} (hb : IsLimit b) (ha : a < b) : succ a < b := by
  rcases (succ_le_iff_lt a b).mpr ha with h | h
  · exact h
  · exact False.elim (hb.2 ⟨a, h.symm⟩)

theorem I_strict (s : Supply) (r : O) {a b : O} (hab : a < b) :
    I s r a < I s r b := by
  induction b using lt_wellFounded.induction generalizing a with
  | h b ih =>
    classical
    by_cases hz : b = 0
    · exact False.elim (not_lt_zero a (hz ▸ hab))
    by_cases hs : ∃ c, b = succ c
    · obtain ⟨c, rfl⟩ := hs
      rw [I_succ]
      have hac : I s r a ≤ I s r c := by
        rcases (lt_succ_iff_le a c).mp hab with h | rfl
        · exact Or.inl (ih c (lt_succ_self c) h)
        · exact le_refl _
      exact lt_of_le_of_lt hac (next_spec s r (I s r c)).1
    · have ha := succ_lt_limit ⟨hz, hs⟩ hab
      obtain ⟨x, hx⟩ := initial_surjective b (succ a) ha
      rw [I_limit s r b hz hs]
      apply lt_of_lt_of_le (ih (succ a) ha (lt_succ_self a))
      have hh := le_sup (fun x : (representative b).Carrier =>
        I s r (type ((representative b).below x))) x
      rwa [← hx] at hh

theorem I_mono (s : Supply) (r : O) {a b : O} (hab : a ≤ b) :
    I s r a ≤ I s r b := by
  rcases hab with h | rfl
  · exact Or.inl (I_strict s r h)
  · exact le_refl _

/-- A countable fundamental sequence for a limit ordinal. -/
structure FundamentalSequence (a : O) (f : Nat → O) : Prop where
  below : ∀ n, f n < a
  strict : ∀ n m, n < m → f n < f m
  cofinal : ∀ x, x < a → ∃ n, x < f n

theorem FundamentalSequence.mono {a : O} {f : Nat → O}
    (h : FundamentalSequence a f) {n m : Nat} (hnm : n ≤ m) : f n ≤ f m := by
  rcases Nat.lt_or_eq_of_le hnm with hn | rfl
  · exact Or.inl (h.strict n m hn)
  · exact le_refl _

theorem FundamentalSequence.sup_eq {a : O} {f : Nat → O}
    (h : FundamentalSequence a f) : sup f = a := by
  apply le_antisymm ((sup_le_iff f a).mpr (fun n => Or.inl (h.below n)))
  apply (not_lt_iff_le _ _).mp
  intro ha
  obtain ⟨n, hn⟩ := h.cofinal _ ha
  exact lt_irrefl _ (lt_of_lt_of_le hn (le_sup f n))

theorem FundamentalSequence.shift {a : O} {f : Nat → O}
    (h : FundamentalSequence a f) (offset : Nat) :
    FundamentalSequence a (fun n => f (n + offset)) := by
  refine ⟨fun n => h.below _, fun n m hnm => h.strict _ _ (by omega), ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := h.cofinal x hx
  exact ⟨n, lt_of_lt_of_le hn (h.mono (by omega))⟩

theorem FundamentalSequence.isLimit {a : O} {f : Nat → O}
    (h : FundamentalSequence a f) : IsLimit a := by
  constructor
  · intro hz
    exact not_lt_zero _ (hz ▸ h.below 0)
  · rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := h.cofinal b (hb ▸ lt_succ_self b)
    have hl := h.below n
    rw [hb, lt_succ_iff_le] at hl
    exact lt_irrefl _ (lt_of_lt_of_le hn hl)

theorem finite_strict {n m : Nat} (h : n < m) : finite n < finite m :=
  (lt_finite_iff _ m).mpr ⟨n, h, rfl⟩

theorem omega_fundamentalSequence : FundamentalSequence omega finite := by
  refine ⟨finite_lt_omega, fun _ _ h => finite_strict h, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := (lt_omega_iff x).mp hx
  exact ⟨n + 1, lt_succ_self _⟩

/-- The limit clause for I carries valid sequences to valid sequences. -/
theorem I_fundamentalSequence (s : Supply) (r a : O) (f : Nat → O)
    (hf : FundamentalSequence a f) :
    FundamentalSequence (I s r a) (fun n => I s r (f n)) := by
  refine ⟨fun n => I_strict s r (hf.below n),
    fun n m h => I_strict s r (hf.strict n m h), ?_⟩
  intro x hx
  rw [I_limit s r a hf.isLimit.1 hf.isLimit.2, lt_sup_iff] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨n, hn⟩ := hf.cofinal _ (initial_lt a y)
  exact ⟨n, lt_trans _ _ _ hy (I_strict s r hn)⟩

/-- Addition on the left preserves fundamental sequences (the sum clause). -/
theorem add_fundamentalSequence (b a : O) (f : Nat → O)
    (hf : FundamentalSequence a f) :
    FundamentalSequence (b + a) (fun n => b + f n) := by
  refine ⟨fun n => add_lt_add_right b (hf.below n),
    fun n m h => add_lt_add_right b (hf.strict n m h), ?_⟩
  intro x hx
  rcases (lt_add_iff b a x).mp hx with hb | ⟨y, hy, hxy⟩
  · exact ⟨0, lt_of_lt_of_le hb (le_add b (f 0))⟩
  · obtain ⟨n, hn⟩ := hf.cofinal y hy
    exact ⟨n, lt_of_le_of_lt hxy (add_lt_add_right b hn)⟩

theorem C_directed_sup (s : Supply) (f g : Nat → O)
    (hf : ∀ n m, n ≤ m → f n ≤ f m) (hg : ∀ n m, n ≤ m → g n ≤ g m)
    (x : O) (hx : C s (sup f) (sup g) x) : ∃ n, C s (f n) (g n) x := by
  have promote (n m : Nat) (hnm : n ≤ m) (x : O) (hx : C s (f n) (g n) x) :
      C s (f m) (g m) x :=
    C_mono_seed s _ _ _ (hg n m hnm) x
      (C_mono_argument s _ _ _ (hf n m hnm) x hx)
  have combine (x y : O) (hx : ∃ n, C s (f n) (g n) x)
      (hy : ∃ n, C s (f n) (g n) y) :
      ∃ n, C s (f n) (g n) x ∧ C s (f n) (g n) y := by
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m, promote n _ (Nat.le_max_left _ _) x hn,
      promote m _ (Nat.le_max_right _ _) y hm⟩
  apply C_least s (sup f) (sup g) (fun x => ∃ n, C s (f n) (g n) x) _ _ _ _ _ x hx
  · exact ⟨0, C_zero s _ _⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (lt_sup_iff g x).mp hx
    exact ⟨n, C_seed s _ _ x hn⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_add s _ _ x y hn hm⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_index s _ _ x y hn hm⟩
  · intro k b hb hk hx hy
    obtain ⟨n, hn, hm⟩ := combine k b hx hy
    obtain ⟨m, hb⟩ := (lt_sup_iff f b).mp hb
    exact ⟨max n m, C_collapse s _ _ k b
      (lt_of_lt_of_le hb (hf m _ (Nat.le_max_right _ _))) hk
      (promote n _ (Nat.le_max_left _ _) k hn)
      (promote n _ (Nat.le_max_left _ _) b hm)⟩

/-- Countable continuity follows from finitariness of the defining closure. -/
theorem psi_sup (s : Supply) (k : O) (f : Nat → O)
    (hf : ∀ n m, n ≤ m → f n ≤ f m) :
    psi s k (sup f) = sup (fun n => psi s k (f n)) := by
  let g := fun n => psi s k (f n)
  have hg : ∀ n m, n ≤ m → g n ≤ g m := fun n m h => psi_mono s k _ _ (hf n m h)
  apply le_antisymm
  · apply psi_min
    refine ⟨(sup_le_iff g k).mpr (fun n => psi_le s k (f n)), ?_⟩
    intro x hx hxk
    obtain ⟨n, hn⟩ := C_directed_sup s f g hf hg x hx
    exact lt_of_lt_of_le (psi_closed s k (f n) x hn hxk) (le_sup g n)
  · exact (sup_le_iff g _).mpr (fun n => psi_mono s k _ _ (le_sup f n))

/-- Strictness requires admissible arguments; psi is not globally strict. -/
theorem psi_strict_of_mem (s : Supply) (k a b : O) (hk : RegularIndex s k)
    (hab : a < b) (hka : C s a (psi s k a) k) (haa : C s a (psi s k a) a) :
    psi s k a < psi s k b := by
  have promote (x : O) (hx : C s a (psi s k a) x) : C s b (psi s k b) x :=
    C_mono_seed s b _ _ (psi_mono s k a b (Or.inl hab)) x
      (C_mono_argument s a b _ (Or.inl hab) x hx)
  exact psi_closed s k b _
    (C_collapse s b _ k a hab hk (promote k hka) (promote a haa))
    (psi_lt s k a (regularIndex_regular s k hk))

/-- The countable-limit psi clause, with explicit normal-form premises. -/
theorem psi_fundamentalSequence (s : Supply) (k a : O) (f : Nat → O)
    (hk : RegularIndex s k) (hf : FundamentalSequence a f)
    (hindex : ∀ n, C s (f n) (psi s k (f n)) k)
    (harg : ∀ n, C s (f n) (psi s k (f n)) (f n)) :
    FundamentalSequence (psi s k a) (fun n => psi s k (f n)) := by
  refine ⟨fun n => psi_strict_of_mem s k (f n) a hk (hf.below n) (hindex n) (harg n),
    fun n m h => psi_strict_of_mem s k (f n) (f m) hk (hf.strict n m h)
      (hindex n) (harg n), ?_⟩
  intro x hx
  rw [← hf.sup_eq, psi_sup s k f (fun n m h => hf.mono h), lt_sup_iff] at hx
  exact hx

end
end OCF.Denis
