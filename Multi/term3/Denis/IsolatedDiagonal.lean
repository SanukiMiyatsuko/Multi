import Multi.term3.Denis.LargeLimitCases

/-! The diagonal construction for isolated large limits.

Let `(k, a)` be proper and `D = C(a, psi k a)`. Suppose `x` is a monotone
sequence of represented elements of `D` below `a` such that every element
of `C(x n, psi k (x n))` below `a` lies below `x (n + 1)`. Then the values
`psi k (x n)` are cofinal in `psi k a`, each is strictly below it, and
`n ↦ psi k (x n) + n` is a covering sequence of length `ω`. This is the
argument of `C_regularArgument_sup` with the regular argument replaced by
an arbitrary isolated argument. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem hasCoveringSequence_of_nat (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (g : Nat → OCF.Denis.O) (hg : OCF.Denis.FundamentalSequence a g)
    (hrep : ∀ n, Represented s (g n)) : HasCoveringSequence s a := by
  intro ha
  have hcof : OCF.Denis.cofinality a ha = OCF.Denis.omega :=
    OCF.Denis.cofinality_eq_omega_of_fundamentalSequence hg
  rw [hcof]
  exact ⟨omega_represented s, _, coveringFundamentalSequence_of_omega s a _
    ⟨hg.transfinite, fun _ _ _ => hrep _⟩⟩

theorem hasCoveringSequence_psi_diagonal (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hp : OCF.Denis.ProperCollapse s k a) (hkrep : Represented s k) (ha0 : 0 < a)
    (x : Nat → OCF.Denis.O)
    (hxD : ∀ n, OCF.Denis.C s a (OCF.Denis.psi s k a) (x n))
    (hxa : ∀ n, x n < a)
    (hxrep : ∀ n, Represented s (x n))
    (hxmono : ∀ n, x n ≤ x (n + 1))
    (hxbound : ∀ n b, OCF.Denis.C s (x n) (OCF.Denis.psi s k (x n)) b → b < a →
      b < x (n + 1)) :
    HasCoveringSequence s (OCF.Denis.psi s k a) := by
  have hk := hp.1
  have hreg := OCF.Denis.regularIndex_regular s k hk
  have hmono : ∀ n m, n ≤ m → x n ≤ x m := by
    intro n m hnm
    induction m with
    | zero =>
      have : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst this
      exact le_refl _
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le hnm with h | rfl
      · exact OCF.Ordinal.le_trans (ih (Nat.le_of_lt_succ h)) (hxmono m)
      · exact le_refl _
  let v : Nat → OCF.Denis.O := fun n => OCF.Denis.psi s k (x n)
  have hvmono : ∀ n m, n ≤ m → v n ≤ v m :=
    fun n m hnm => OCF.Denis.psi_mono s k _ _ (hmono n m hnm)
  have hvlt : ∀ n, v n < OCF.Denis.psi s k a := by
    intro n
    rcases OCF.Denis.psi_mono s k (x n) a (Or.inl (hxa n)) with h | heq
    · exact h
    · exfalso
      obtain ⟨_, _, hgap⟩ := OCF.Denis.psi_proper_plateau s k a k (x n) hk hk hp.2.1 hp.2.2 heq
      exact hgap (x n) (hxD n) (le_refl _) (hxa n)
  have promote : ∀ n m, n ≤ m → ∀ z, OCF.Denis.C s (x n) (v n) z → OCF.Denis.C s (x m) (v m) z :=
    fun n m hnm z hz => OCF.Denis.C_mono_seed s _ _ _ (hvmono n m hnm) z
      (OCF.Denis.C_mono_argument s _ _ _ (hmono n m hnm) z hz)
  have combine : ∀ z w, (∃ n, OCF.Denis.C s (x n) (v n) z) → (∃ n, OCF.Denis.C s (x n) (v n) w) →
      ∃ n, OCF.Denis.C s (x n) (v n) z ∧ OCF.Denis.C s (x n) (v n) w := by
    rintro z w ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, promote n _ (Nat.le_max_left _ _) z hn, promote m _ (Nat.le_max_right _ _) w hm⟩
  have hstage : ∀ z, OCF.Denis.C s a (OCF.Ordinal.sup v) z → ∃ n, OCF.Denis.C s (x n) (v n) z := by
    intro z hz
    apply OCF.Denis.C_least s a (OCF.Ordinal.sup v) (fun z => ∃ n, OCF.Denis.C s (x n) (v n) z)
      _ _ _ _ _ z hz
    · exact ⟨0, OCF.Denis.C_zero s _ _⟩
    · intro z hz
      obtain ⟨n, hn⟩ := (OCF.Ordinal.lt_sup_iff v z).mp hz
      exact ⟨n, OCF.Denis.C_seed s _ _ z hn⟩
    · intro z w hz hw
      obtain ⟨n, hn, hm⟩ := combine z w hz hw
      exact ⟨n, OCF.Denis.C_add s _ _ z w hn hm⟩
    · intro z w hz hw
      obtain ⟨n, hn, hm⟩ := combine z w hz hw
      exact ⟨n, OCF.Denis.C_index s _ _ z w hn hm⟩
    · intro j b hb hj hjP hbP
      obtain ⟨n, hn, hm⟩ := combine j b hjP hbP
      exact ⟨n + 1, OCF.Denis.C_collapse s _ _ j b (hxbound n b hm hb) hj
        (promote n _ (Nat.le_succ n) j hn) (promote n _ (Nat.le_succ n) b hm)⟩
  have hsup : OCF.Denis.psi s k a ≤ OCF.Ordinal.sup v := by
    apply OCF.Denis.psi_min s k a (OCF.Ordinal.sup v)
    refine ⟨(OCF.Ordinal.sup_le_iff v k).mpr (fun n => OCF.Denis.psi_le s k (x n)), ?_⟩
    intro z hz hzk
    obtain ⟨n, hn⟩ := hstage z hz
    exact OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.psi_closed s k (x n) z hn hzk)
      (OCF.Ordinal.le_sup v n)
  have hfin : ∀ n, OCF.Denis.finite n < OCF.Denis.psi s k a := by
    intro n
    exact OCF.Denis.psi_closed s k a _ (OCF.Denis.C_finite s a _ ha0 n)
      (OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.finite_lt_omega n) hreg.1)
  have hprin := OCF.Denis.psi_addPrincipal s k a hreg
  refine hasCoveringSequence_of_nat s _ (fun n => v n + OCF.Denis.finite n) ⟨?_, ?_, ?_⟩ ?_
  · intro n
    exact hprin _ _ (hvlt n) (hfin n)
  · intro n m hnm
    exact OCF.Ordinal.lt_of_le_of_lt (add_mono_left (hvmono n m (Nat.le_of_lt hnm)) _)
      (add_lt_add_right _ (OCF.Denis.finite_strict hnm))
  · intro z hz
    obtain ⟨n, hn⟩ := (OCF.Ordinal.lt_sup_iff v z).mp (OCF.Ordinal.lt_of_lt_of_le hz hsup)
    exact ⟨n, OCF.Ordinal.lt_of_lt_of_le hn (le_add _ _)⟩
  · intro n
    exact represented_add s _ _ (represented_psi s k (x n) hkrep (hxrep n) hk)
      (finite_represented s n)

/-- Every earlier stage closure has a represented strict upper bound below
the argument inside the parent closure. -/
def IsolatedStageBound (s : OCF.Denis.Supply) (k a : OCF.Denis.O) : Prop :=
  ∀ y, Represented s y → OCF.Denis.C s a (OCF.Denis.psi s k a) y → y < a →
    ∃ y', Represented s y' ∧ OCF.Denis.C s a (OCF.Denis.psi s k a) y' ∧ y' < a ∧ y ≤ y' ∧
      ∀ b, OCF.Denis.C s y (OCF.Denis.psi s k y) b → b < a → b < y'

theorem hasCoveringSequence_of_stageBound (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hp : OCF.Denis.ProperCollapse s k a) (hkrep : Represented s k) (ha0 : 0 < a)
    (h : IsolatedStageBound s k a) : HasCoveringSequence s (OCF.Denis.psi s k a) := by
  classical
  let P : OCF.Denis.O → Prop := fun y =>
    Represented s y ∧ OCF.Denis.C s a (OCF.Denis.psi s k a) y ∧ y < a
  have h0 : P 0 := ⟨represented_zero s, OCF.Denis.C_zero s _ _, ha0⟩
  let next : {y // P y} → {y // P y} := fun y =>
    ⟨Classical.choose (h y.1 y.2.1 y.2.2.1 y.2.2.2),
      (Classical.choose_spec (h y.1 y.2.1 y.2.2.1 y.2.2.2)).1,
      (Classical.choose_spec (h y.1 y.2.1 y.2.2.1 y.2.2.2)).2.1,
      (Classical.choose_spec (h y.1 y.2.1 y.2.2.1 y.2.2.2)).2.2.1⟩
  have hnext : ∀ y : {y // P y}, y.1 ≤ (next y).1 ∧
      ∀ b, OCF.Denis.C s y.1 (OCF.Denis.psi s k y.1) b → b < a → b < (next y).1 :=
    fun y => (Classical.choose_spec (h y.1 y.2.1 y.2.2.1 y.2.2.2)).2.2.2
  let seq : Nat → {y // P y} := fun n => Nat.rec ⟨0, h0⟩ (fun _ y => next y) n
  have hseq : ∀ n, seq (n + 1) = next (seq n) := fun _ => rfl
  apply hasCoveringSequence_psi_diagonal s k a hp hkrep ha0 (fun n => (seq n).1)
    (fun n => (seq n).2.2.1) (fun n => (seq n).2.2.2) (fun n => (seq n).2.1)
  · intro n
    rw [hseq n]
    exact (hnext (seq n)).1
  · intro n b hb hba
    rw [hseq n]
    exact (hnext (seq n)).2 b hb hba

/-- The isolated large limit case follows from the stage bound. -/
theorem isolatedLargeLimitStep_of_stageBound (s : OCF.Denis.Supply)
    (h : ∀ k a, IsNormal s (.psi k a) → OCF.Denis.IsLimit (denote s a) →
      ¬ OCF.Denis.UncountableRegular (denote s a) → denote s k ≤ denote s a →
      OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) →
      (∃ c, c < denote s a ∧ OCF.Denis.psi s (denote s k) c = denote s (.psi k a)) →
      IsolatedStageBound s (denote s k) (denote s a)) :
    IsolatedLargeLimitStep s := by
  intro k a hn ha hnreg hka hK hiso _
  have hp : OCF.Denis.ProperCollapse s (denote s k) (denote s a) := by
    cases hn with
    | collapse hk _ hreg harg => exact ⟨hreg, hK, harg⟩
  have hkrep : Represented s (denote s k) := by
    cases hn with
    | collapse hk _ _ _ => exact ⟨k, hk, rfl⟩
  exact hasCoveringSequence_of_stageBound s _ _ hp hkrep
    ((zero_lt_iff_ne_zero _).mpr ha.1) (h k a hn ha hnreg hka hK hiso)

end
end T.Correspondence.Denis.Covering
