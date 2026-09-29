import Multi.term3.Denis.NestedIndex

/-! Termination and preservation for nested-index elimination at arbitrary
subterm positions. Irreducibility here is with respect to this proved
rule, not a claim that all semantic duplication has been eliminated. -/

namespace T.Correspondence.Denis.Covering.Nested
open OCF.Ordinal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

inductive Step (s : OCF.Denis.Supply) : Term → Term → Prop where
  | nested {q r b t a : Term} : denote s q < denote s r →
      OCF.Denis.RegularIndex s (denote s (.I r b)) → denote s a ≤ denote s t →
      Step s (nestedCollapse q r b t a) (.psi (.I r b) a)
  | addLeft {a a' b : Term} : Step s a a' → Step s (.add a b) (.add a' b)
  | addRight {a b b' : Term} : Step s b b' → Step s (.add a b) (.add a b')
  | indexRank {r r' b : Term} : Step s r r' → Step s (.I r b) (.I r' b)
  | indexArgument {r b b' : Term} : Step s b b' → Step s (.I r b) (.I r b')
  | collapseIndex {k k' a : Term} : Step s k k' → Step s (.psi k a) (.psi k' a)
  | collapseArgument {k a a' : Term} : Step s a a' → Step s (.psi k a) (.psi k a')

theorem Step.value_eq {s : OCF.Denis.Supply} {a b : Term} (h : Step s a b) : denote s a = denote s b := by
  induction h with
  | nested hqr hreg hat => exact nestedCollapse_value s _ _ _ _ _ hqr hreg hat
  | addLeft _ ih | addRight _ ih | indexRank _ ih | indexArgument _ ih | collapseIndex _ ih | collapseArgument _ ih => simp only [Denis.denote, ih]

theorem Step.principal {s : OCF.Denis.Supply} {a b : Term} (h : Step s a b) :
    a.isPrincipal ↔ b.isPrincipal := by
  cases h <;> rfl

theorem Step.leading {s : OCF.Denis.Supply} {a b : Term} (h : Step s a b) :
    denote s a.leading = denote s b.leading := by
  induction h with
  | nested hqr hreg hat => exact nestedCollapse_value s _ _ _ _ _ hqr hreg hat
  | addLeft _ ih => exact ih
  | addRight => rfl
  | indexRank h _ => exact (Step.indexRank h).value_eq
  | indexArgument h _ => exact (Step.indexArgument h).value_eq
  | collapseIndex h _ => exact (Step.collapseIndex h).value_eq
  | collapseArgument h _ => exact (Step.collapseArgument h).value_eq

theorem Step.smaller {s : OCF.Denis.Supply} {a b : Term} (h : Step s a b) : sizeOf b < sizeOf a := by
  induction h with
  | nested => exact nestedCollapse_replacement_smaller _ _ _ _ _
  | addLeft _ ih | addRight _ ih | indexRank _ ih | indexArgument _ ih | collapseIndex _ ih | collapseArgument _ ih => simp_all

theorem Step.normal {s : OCF.Denis.Supply} {a b : Term} (h : Step s a b) :
    IsNormal s a → IsNormal s b := by
  induction h with
  | nested hqr _ hat =>
    intro hn
    exact (nestedCollapse_replacement_normal s _ _ _ _ _ hn hqr hat).1
  | addLeft h ih =>
    intro hn
    cases hn with
    | sum ha hb hap hp hbpos hhead =>
      apply IsNormal.sum (ih ha) hb (h.principal.mp hap)
      · simpa only [← h.value_eq] using hp
      · exact hbpos
      · simpa only [← h.value_eq] using hhead
  | addRight h ih =>
    intro hn
    cases hn with
    | sum ha hb hap hp hbpos hhead =>
      apply IsNormal.sum ha (ih hb) hap hp
      · simpa only [← h.value_eq] using hbpos
      · simpa only [← h.leading] using hhead
  | indexRank h ih =>
    intro hn
    cases hn with
    | index hr hb hrl hbl =>
      apply IsNormal.index (ih hr) hb
      · simpa only [← h.value_eq] using hrl
      · simpa only [← h.value_eq] using hbl
  | indexArgument h ih =>
    intro hn
    cases hn with
    | index hr hb hrl hbl =>
      apply IsNormal.index hr (ih hb)
      · simpa only [← h.value_eq] using hrl
      · simpa only [← h.value_eq] using hbl
  | collapseIndex h ih =>
    intro hn
    cases hn with
    | collapse hk ha hreg harg =>
      apply IsNormal.collapse (ih hk) ha
      · simpa only [← h.value_eq] using hreg
      · simpa only [← h.value_eq] using harg
  | collapseArgument h ih =>
    intro hn
    cases hn with
    | collapse hk ha hreg harg =>
      apply IsNormal.collapse hk (ih ha) hreg
      simpa only [← h.value_eq] using harg

inductive Reduces (s : OCF.Denis.Supply) : Term → Term → Prop where
  | refl (a : Term) : Reduces s a a
  | cons {a b c : Term} : Step s a b → Reduces s b c → Reduces s a c

theorem Reduces.value_eq {s : OCF.Denis.Supply} {a b : Term} (h : Reduces s a b) :
    denote s a = denote s b := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact h.value_eq.trans ih

theorem Reduces.normal {s : OCF.Denis.Supply} {a b : Term} (h : Reduces s a b) :
    IsNormal s a → IsNormal s b := by
  induction h with
  | refl => exact fun h => h
  | cons h _ ih => exact fun hn => ih (h.normal hn)

def Irreducible (s : OCF.Denis.Supply) (a : Term) : Prop := ¬ ∃ b, Step s a b

/-- Repeatedly eliminate a nested index wherever the rule applies.
The semantic comparison tests use classical choice. -/
def normalize (s : OCF.Denis.Supply) (a : Term) : Term :=
  if h : ∃ b, Step s a b then normalize s (Classical.choose h) else a
termination_by sizeOf a
decreasing_by exact (Classical.choose_spec h).smaller

theorem normalize_spec (s : OCF.Denis.Supply) (a : Term) :
    Reduces s a (normalize s a) ∧ Irreducible s (normalize s a) := by
  rw [normalize]
  split
  · rename_i h
    have ih := normalize_spec s (Classical.choose h)
    exact ⟨.cons (Classical.choose_spec h) ih.1, ih.2⟩
  · rename_i h
    exact ⟨.refl a, h⟩
termination_by sizeOf a
decreasing_by
  rename_i h
  exact (Classical.choose_spec h).smaller

theorem normalize_normal (s : OCF.Denis.Supply) (a : Term) (ha : IsNormal s a) :
    IsNormal s (normalize s a) := (normalize_spec s a).1.normal ha

theorem denote_normalize (s : OCF.Denis.Supply) (a : Term) :
    denote s (normalize s a) = denote s a := (normalize_spec s a).1.value_eq.symm

theorem normalize_of_irreducible (s : OCF.Denis.Supply) (a : Term) (ha : Irreducible s a) :
    normalize s a = a := by
  rw [normalize, dite_eq_right ha]

theorem normalize_idempotent (s : OCF.Denis.Supply) (a : Term) :
    normalize s (normalize s a) = normalize s a :=
  normalize_of_irreducible s _ (normalize_spec s a).2

theorem revised_normalize_agrees (s : OCF.Denis.Supply) (a : Term) (n : Nat) :
    revisedValue s (denote s (normalize s a)) n = revisedValue s (denote s a) n := by
  rw [denote_normalize]

theorem normalized_fundamentalSequence_iff (s : OCF.Denis.Supply) (a : Term) :
    OCF.Denis.FundamentalSequence (denote s (normalize s a)) (revisedValue s (denote s (normalize s a))) ↔
      OCF.Denis.FundamentalSequence (denote s a) (revisedValue s (denote s a)) := by
  rw [denote_normalize]

end
end T.Correspondence.Denis.Covering.Nested
