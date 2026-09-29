import Multi.term3.Term3DenisNormal
import Multi.term3.Denis.RankBound

/-! Order-theoretic properties of Denis's normal notations. Semantic
well-foundedness and syntactic uniqueness are separate obligations. -/

namespace T.Correspondence.Denis
open OCF.Ordinal
noncomputable section

theorem normal_rankBounded (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    OCF.Denis.RankBounded s (denote s t) := by
  induction ht with
  | zero => exact OCF.Denis.rankBounded_zero s
  | index _ _ _ _ ihr ihb => exact OCF.Denis.rankBounded_I s ihr ihb
  | @collapse k a hk ha hreg harg ihk iha =>
    exact OCF.Denis.rankBounded_down s
      (Or.inl (OCF.Denis.psi_lt s _ _ (OCF.Denis.regularIndex_regular s _ hreg))) ihk
  | sum _ _ _ _ _ _ iha ihb => exact OCF.Denis.rankBounded_add s iha ihb

/-- Rule 10.7 for every finite normal rank notation, with no extra
closure-membership premise. -/
theorem successor_rank_zero_fundamentalSequence (s : OCF.Denis.Supply)
    (r : Term) (hr : IsNormal s r) :
    OCF.Denis.FundamentalSequence
      (OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) 0)
      (OCF.Denis.indexIter s (denote s r)) :=
  OCF.Denis.bounded_rank_zero_fundamentalSequence s _ (normal_rankBounded s r hr)

def indexIterTerm (r : Term) : Nat → Term
  | 0 => .zero
  | n + 1 => .I r (indexIterTerm r n)

theorem denote_indexIterTerm (s : OCF.Denis.Supply) (r : Term) (n : Nat) :
    denote s (indexIterTerm r n) = OCF.Denis.indexIter s (denote s r) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change OCF.Denis.I s (denote s r) (denote s (indexIterTerm r n)) = _
    rw [ih]
    rfl

theorem indexIterTerm_isNormal (s : OCF.Denis.Supply) (r : Term) (hr : IsNormal s r) (n : Nat) :
    IsNormal s (indexIterTerm r n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    apply IsNormal.index hr ih
    · have hl := OCF.Denis.rank_lt_first_of_bounded s _ (normal_rankBounded s r hr)
      have hm := OCF.Denis.I_mono s (denote s r) (zero_le (denote s (indexIterTerm r n)))
      rw [OCF.Denis.I_zero] at hm
      exact OCF.Ordinal.lt_of_lt_of_le hl hm
    · rw [denote_indexIterTerm]
      exact OCF.Denis.indexIter_lt_succ s _ n

def NormalTerm (s : OCF.Denis.Supply) := {t : Term // IsNormal s t}

def NormalLt (s : OCF.Denis.Supply) (a b : NormalTerm s) : Prop :=
  denote s a.1 < denote s b.1

theorem normalLt_wellFounded (s : OCF.Denis.Supply) : WellFounded (NormalLt s) := by
  apply InvImage.wf (fun t : NormalTerm s => denote s t.1) OCF.Ordinal.lt_wellFounded

/-- The represented ordinals, with equality of ordinal values. This does
not yet assert injectivity of the raw normal-syntax denotation. -/
def NormalOrdinal (s : OCF.Denis.Supply) :=
  {a : OCF.Denis.O // ∃ t : Term, IsNormal s t ∧ denote s t = a}

def normalOrdinalWellOrder (s : OCF.Denis.Supply) : OCF.WellOrder.{1} where
  Carrier := NormalOrdinal s
  lt a b := a.1 < b.1
  irrefl a := OCF.Ordinal.lt_irrefl a.1
  trans a b c := OCF.Ordinal.lt_trans a.1 b.1 c.1
  total a b := by
    rcases OCF.Ordinal.lt_total a.1 b.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf (fun a : NormalOrdinal s => a.1) OCF.Ordinal.lt_wellFounded

theorem normalOrdinal_exists_min (s : OCF.Denis.Supply) (P : NormalOrdinal s → Prop)
    (h : ∃ a, P a) : ∃ a, P a ∧ ∀ b, b.1 < a.1 → ¬ P b :=
  OCF.WellOrder.exists_min (normalOrdinalWellOrder s) P h

theorem normal_index_parameters_unique (s : OCF.Denis.Supply) (r b q c : Term)
    (h1 : IsNormal s (.I r b)) (h2 : IsNormal s (.I q c))
    (heq : denote s (.I r b) = denote s (.I q c)) :
    denote s r = denote s q ∧ denote s b = denote s c := by
  cases h1 with
  | index _ _ hr hb =>
    cases h2 with
    | index _ _ hq hc => exact OCF.Denis.I_normal_injective s _ _ _ _ hb hc heq

theorem normal_index_ne_collapse (s : OCF.Denis.Supply) (r b k a : Term)
    (h1 : IsNormal s (.I r b)) (h2 : IsNormal s (.psi k a)) :
    denote s (.I r b) ≠ denote s (.psi k a) := by
  cases h1 with
  | index _ _ hr hb =>
    cases h2 with
    | collapse _ _ hk ha =>
      exact OCF.Denis.I_normal_ne_psi s _ _ _ _ (OCF.Denis.regularIndex_regular s _ hk) hr hb

end
end T.Correspondence.Denis
