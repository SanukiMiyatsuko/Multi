import Multi.term3.Term3DenisOrder

/-! A check of the successor-index zero-argument sequence rule against
the actual closure definition. All inequalities below are ordinal facts. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def obstructionBase (s : Supply) : O := psi s (I s (succ 0) 0) 0
def obstructionIndex (s : Supply) : O := I s 0 (succ (obstructionBase s))
def obstructionValue (s : Supply) : O := psi s (obstructionIndex s) 0

theorem obstructionBase_lt_index (s : Supply) : obstructionBase s < obstructionIndex s :=
  lt_of_lt_of_le (lt_succ_self _) (index_le_I s 0 _)

theorem obstructionIndex_lt_inaccessible (s : Supply) : obstructionIndex s < I s (succ 0) 0 :=
  I_lt_inaccessible s (first_inaccessible s (succ 0)) 0 _ (lt_succ_self 0)
    (regular_succ_lt (inaccessible_regular (first_inaccessible s (succ 0)))
      (psi_lt s _ 0 (inaccessible_regular (first_inaccessible s (succ 0)))))

theorem obstructionIndex_regular (s : Supply) : RegularIndex s (obstructionIndex s) :=
  Or.inr ⟨0, obstructionBase s, rfl⟩

/-- The closure for the larger index supplies an upper bound for this value. -/
theorem obstructionValue_le_base (s : Supply) : obstructionValue s ≤ obstructionBase s := by
  apply psi_min
  refine ⟨Or.inl (obstructionBase_lt_index s), ?_⟩
  intro x hx hxk
  exact psi_closed s (I s (succ 0) 0) 0 x hx
    (lt_trans _ _ _ hxk (obstructionIndex_lt_inaccessible s))

theorem obstructionValue_eq_base (s : Supply) : obstructionValue s = obstructionBase s := by
  apply le_antisymm (obstructionValue_le_base s)
  have heq := indexIter_sup_eq_psi_first_succ_rank s 0 (C_zero s _ _)
  change sup (indexIter s 0) = obstructionBase s at heq
  rw [← heq]
  have hc : ∀ n, C s 0 (obstructionValue s) (indexIter s 0 n) := by
    intro n
    induction n with
    | zero => exact C_zero s _ _
    | succ n ih => exact C_index s _ _ 0 _ (C_zero s _ _) ih
  apply (sup_le_iff _ _).mpr
  intro n
  have hn := indexIter_lt_sup s 0 n
  rw [heq] at hn
  exact Or.inl (psi_closed s _ _ _ (hc n)
    (lt_trans _ _ _ hn (obstructionBase_lt_index s)))

theorem obstructionBase_fixedpoint (s : Supply) : I s 0 (obstructionBase s) = obstructionBase s := by
  have heq := indexIter_sup_eq_psi_first_succ_rank s 0 (C_zero s _ _)
  change sup (indexIter s 0) = obstructionBase s at heq
  rw [← heq]
  exact indexIter_sup_fixedpoint s 0

theorem obstruction_base_not_below (s : Supply) : ¬ obstructionBase s < obstructionValue s :=
  (not_lt_iff_le _ _).mpr (obstructionValue_le_base s)

/-- The unnormalised I(0,b) version also fails the descent condition. -/
theorem obstruction_I_base_not_below (s : Supply) :
    ¬ I s 0 (obstructionBase s) < obstructionValue s :=
  (not_lt_iff_le _ _).mpr (le_trans (obstructionValue_le_base s) (index_le_I s 0 _))

theorem obstruction_not_fundamentalSequence (s : Supply) (f : Nat → O)
    (h : f 1 = obstructionBase s) : ¬ FundamentalSequence (obstructionValue s) f := by
  intro hf
  have hh := hf.below 1
  rw [h] at hh
  exact obstruction_base_not_below s hh

end
end OCF.Denis

namespace T.Correspondence.Denis
open OCF.Ordinal
noncomputable section

def obstructionIndexTerm : Term := .I .zero (.add cardFixed one)
def obstructionTerm : Term := .psi obstructionIndexTerm .zero

theorem denote_cardFixed (s : OCF.Denis.Supply) :
    denote s cardFixed = OCF.Denis.obstructionBase s := by
  change OCF.Denis.psi s (denote s I1) 0 = _
  rw [denote_I1]
  rfl

theorem denote_obstructionIndexTerm (s : OCF.Denis.Supply) :
    denote s obstructionIndexTerm = OCF.Denis.obstructionIndex s := by
  change OCF.Denis.I s 0 (denote s cardFixed + denote s one) = _
  rw [denote_cardFixed, denote_one, add_succ, add_zero]
  rfl

theorem denote_obstructionTerm (s : OCF.Denis.Supply) :
    denote s obstructionTerm = OCF.Denis.obstructionValue s := by
  change OCF.Denis.psi s (denote s obstructionIndexTerm) 0 = _
  rw [denote_obstructionIndexTerm]
  rfl

theorem cardFixed_isNormal (s : OCF.Denis.Supply) : IsNormal s cardFixed := by
  apply IsNormal.collapse (I1_isNormal s) .zero
  · rw [denote_I1]
    exact Or.inl ⟨succ 0, rfl⟩
  · exact OCF.Denis.C_zero s _ _

theorem obstructionIndexTerm_isNormal (s : OCF.Denis.Supply) : IsNormal s obstructionIndexTerm := by
  have hreg : OCF.Denis.UncountableRegular (denote s I1) := by
    rw [denote_I1]
    exact OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ 0, rfl⟩)
  have hp : 0 < denote s cardFixed := OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos hreg)
  have hadd : IsNormal s (.add cardFixed one) := by
    apply IsNormal.sum (cardFixed_isNormal s) (one_isNormal s) (by trivial)
      (OCF.Denis.psi_addPrincipal s _ _ hreg)
    · rw [denote_one]; exact lt_succ_self 0
    · change denote s one ≤ denote s cardFixed
      rw [denote_one]
      exact (succ_le_iff_lt _ _).mpr hp
  apply IsNormal.index .zero hadd
  · change 0 < denote s obstructionIndexTerm
    rw [denote_obstructionIndexTerm]
    exact OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (OCF.Denis.obstructionIndex_regular s))
  · change denote s cardFixed + denote s one < denote s obstructionIndexTerm
    rw [denote_cardFixed, denote_one, add_succ, add_zero, denote_obstructionIndexTerm]
    exact OCF.Denis.regular_succ_lt
      (OCF.Denis.regularIndex_regular s _ (OCF.Denis.obstructionIndex_regular s))
      (OCF.Denis.obstructionBase_lt_index s)

theorem obstructionTerm_isNormal (s : OCF.Denis.Supply) : IsNormal s obstructionTerm := by
  apply IsNormal.collapse (obstructionIndexTerm_isNormal s) .zero
  · rw [denote_obstructionIndexTerm]
    exact OCF.Denis.obstructionIndex_regular s
  · exact OCF.Denis.C_zero s _ _

/-- A finite normal term, with a proposed first sequence element that is
not smaller than the term's denotation. -/
theorem obstruction_normal_and_not_descending (s : OCF.Denis.Supply) :
    IsNormal s obstructionTerm ∧ ¬ denote s cardFixed < denote s obstructionTerm := by
  refine ⟨obstructionTerm_isNormal s, ?_⟩
  rw [denote_cardFixed, denote_obstructionTerm]
  exact OCF.Denis.obstruction_base_not_below s

theorem obstruction_normal_distinct_same_value (s : OCF.Denis.Supply) :
    IsNormal s cardFixed ∧ IsNormal s obstructionTerm ∧
      cardFixed ≠ obstructionTerm ∧ denote s cardFixed = denote s obstructionTerm := by
  refine ⟨cardFixed_isNormal s, obstructionTerm_isNormal s, by decide, ?_⟩
  rw [denote_cardFixed, denote_obstructionTerm, OCF.Denis.obstructionValue_eq_base]

theorem normal_denotation_not_injective (s : OCF.Denis.Supply) :
    ¬ ∀ a b : NormalTerm s, denote s a.1 = denote s b.1 → a = b := by
  intro h
  have hc := obstruction_normal_distinct_same_value s
  have heq := h ⟨cardFixed, hc.1⟩ ⟨obstructionTerm, hc.2.1⟩ hc.2.2.2
  exact hc.2.2.1 (congrArg Subtype.val heq)

end
end T.Correspondence.Denis
