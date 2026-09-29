import Multi.term3.Denis.RevisedSequences

/-! Normal output terms, a well-order of representatives, and coverage of
the whole normal-ordinal range. Equal-denotation presentations are given
one representative; the OCF itself and its normal-value range are unchanged.
-/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

def termOf (s : OCF.Denis.Supply) (a : NormalOrdinal s) : Term := Classical.choose a.2

theorem termOf_normal (s : OCF.Denis.Supply) (a : NormalOrdinal s) : IsNormal s (termOf s a) :=
  (Classical.choose_spec a.2).1

theorem denote_termOf (s : OCF.Denis.Supply) (a : NormalOrdinal s) : denote s (termOf s a) = a.1 :=
  (Classical.choose_spec a.2).2

def normalise (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) : Term :=
  termOf s ⟨denote s t, t, ht, rfl⟩

theorem normalise_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    IsNormal s (normalise s t ht) := termOf_normal s _

theorem denote_normalise (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    denote s (normalise s t ht) = denote s t := denote_termOf s _

theorem normalise_eq_of_denote_eq (s : OCF.Denis.Supply) (t u : Term)
    (ht : IsNormal s t) (hu : IsNormal s u) (h : denote s t = denote s u) :
    normalise s t ht = normalise s u hu := congrArg (termOf s) (Subtype.ext h)

theorem normalise_idempotent (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    normalise s (normalise s t ht) (normalise_normal s t ht) = normalise s t ht :=
  normalise_eq_of_denote_eq s _ _ _ _ (denote_normalise s t ht)

def CanonicalTerm (s : OCF.Denis.Supply) :=
  {t : Term // ∃ ht : IsNormal s t, normalise s t ht = t}

def canonical (s : OCF.Denis.Supply) (a : NormalOrdinal s) : CanonicalTerm s :=
  ⟨termOf s a, termOf_normal s a, by
    apply congrArg (termOf s)
    exact Subtype.ext (denote_termOf s a)⟩

theorem canonical_denote_injective (s : OCF.Denis.Supply) (a b : CanonicalTerm s)
    (h : denote s a.1 = denote s b.1) : a = b := by
  obtain ⟨ha, hea⟩ := a.2
  obtain ⟨hb, heb⟩ := b.2
  apply Subtype.ext
  rw [← hea, ← heb]
  exact normalise_eq_of_denote_eq s _ _ ha hb h

def canonicalWellOrder (s : OCF.Denis.Supply) : OCF.WellOrder.{0} where
  Carrier := CanonicalTerm s
  lt a b := denote s a.1 < denote s b.1
  irrefl a := OCF.Ordinal.lt_irrefl _
  trans a b c := OCF.Ordinal.lt_trans _ _ _
  total a b := by
    rcases OCF.Ordinal.lt_total (denote s a.1) (denote s b.1) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (canonical_denote_injective s a b h))
    · exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf (fun a : CanonicalTerm s => denote s a.1) OCF.Ordinal.lt_wellFounded

/-- No normal ordinal value is lost by selecting representatives. -/
theorem canonical_covers_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    ∃ c : CanonicalTerm s, denote s c.1 = denote s t :=
  ⟨canonical s ⟨denote s t, t, ht, rfl⟩, denote_termOf s _⟩

def expandedTerm (s : OCF.Denis.Supply) (a : NormalOrdinal s) (n : Nat) : Term :=
  termOf s (revisedStep s a n)

theorem expandedTerm_normal (s : OCF.Denis.Supply) (a : NormalOrdinal s) (n : Nat) :
    IsNormal s (expandedTerm s a n) := termOf_normal s _

theorem expandedTerm_denote (s : OCF.Denis.Supply) (a : NormalOrdinal s) (n : Nat) :
    denote s (expandedTerm s a n) = revisedValue s a.1 n := denote_termOf s _

def rankTowerTerm : Nat → Term
  | 0 => .zero
  | n + 1 => .I (rankTowerTerm n) .zero

theorem denote_rankTowerTerm (s : OCF.Denis.Supply) (n : Nat) :
    denote s (rankTowerTerm n) = OCF.Denis.rankTower s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change OCF.Denis.I s (denote s (rankTowerTerm n)) 0 = _
    rw [ih]
    rfl

theorem rankTowerTerm_normal (s : OCF.Denis.Supply) (n : Nat) : IsNormal s (rankTowerTerm n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    apply IsNormal.index ih .zero
    · rw [denote_rankTowerTerm]
      exact OCF.Denis.rankTower_lt_succ s n
    · rw [denote_rankTowerTerm]
      exact OCF.Ordinal.lt_of_le_of_lt (zero_le _) (OCF.Denis.rankTower_lt_succ s n)

def root (s : OCF.Denis.Supply) (n : Nat) : NormalOrdinal s :=
  ⟨OCF.Denis.rankTower s n, rankTowerTerm n, rankTowerTerm_normal s n, denote_rankTowerTerm s n⟩

/-- Every normal ordinal, including the uncountable parameters, occurs in
a finite expansion path from some root of the rank tower. -/
theorem all_normal_ordinals_reachable (s : OCF.Denis.Supply) (b : NormalOrdinal s) :
    ∃ n ns, follow s (root s n) ns = b := by
  obtain ⟨t, ht, heq⟩ := b.2
  obtain ⟨n, hn⟩ := normal_rankBounded s t ht
  rw [heq] at hn
  obtain ⟨ns, hns⟩ := follow_exists_of_lt s (root s n) b hn
  exact ⟨n, ns, hns⟩

theorem all_normal_terms_reachable (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    ∃ n ns, denote s (termOf s (follow s (root s n) ns)) = denote s t := by
  obtain ⟨n, ns, h⟩ := all_normal_ordinals_reachable s ⟨denote s t, t, ht, rfl⟩
  refine ⟨n, ns, ?_⟩
  rw [denote_termOf, h]

theorem revised_limit_strict (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) (n m : Nat) (h : n < m) : revisedValue s a n < revisedValue s a m := by
  rw [revisedValue_limit s a ha n, revisedValue_limit s a ha m]
  exact strictValue_strict s a ha h

theorem revised_limit_cofinal_among_normal (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : NormalLimit s a) (b : OCF.Denis.O) (hb : Represented s b) (hba : b < a) :
    ∃ n, b < revisedValue s a n := by
  obtain ⟨n, hn⟩ := strictValue_covers s a b ha hb hba
  exact ⟨n, by rw [revisedValue_limit s a ha]; exact hn⟩

end
end T.Correspondence.Denis.Covering
