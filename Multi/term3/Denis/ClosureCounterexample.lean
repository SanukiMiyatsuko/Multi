import Multi.term3.Denis.CollapseUniqueness

/-! Why arbitrary raw normal collapse indices cannot be recovered from
membership of the collapse value in C. This rules out an invalid shortcut
when extending the IndexTree approximation theorem to large collapses. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def closureCounterUpper (s : Supply) : O := psi s (I s (succ 0) 0) (succ 0)
def closureCounterIndex (s : Supply) : O := I s 0 (succ (closureCounterUpper s))

theorem closureCounterUpper_lt_index (s : Supply) : closureCounterUpper s < closureCounterIndex s :=
  lt_of_lt_of_le (lt_succ_self _) (index_le_I s 0 _)

theorem closureCounterIndex_regular (s : Supply) : RegularIndex s (closureCounterIndex s) :=
  Or.inr ⟨0, closureCounterUpper s, rfl⟩

theorem closureCounterIndex_lt_inaccessible (s : Supply) : closureCounterIndex s < I s (succ 0) 0 :=
  I_lt_inaccessible s (first_inaccessible s (succ 0)) 0 _ (lt_succ_self 0)
    (regular_succ_lt (inaccessible_regular (first_inaccessible s (succ 0)))
      (psi_lt s _ _ (inaccessible_regular (first_inaccessible s (succ 0)))))

theorem base_lt_closureCounterIndex (s : Supply) : obstructionBase s < closureCounterIndex s :=
  lt_of_le_of_lt (psi_mono s _ 0 (succ 0) (zero_le _)) (closureCounterUpper_lt_index s)

theorem closureCounterValue_eq_base (s : Supply) : psi s (closureCounterIndex s) 0 = obstructionBase s := by
  apply le_antisymm
  · exact psi_mono_index s _ _ 0 (Or.inl (closureCounterIndex_lt_inaccessible s))
  · have heq := indexIter_sup_eq_psi_first_succ_rank s 0 (C_zero s _ _)
    change sup (indexIter s 0) = obstructionBase s at heq
    rw [← heq]
    have hc : ∀ n, C s 0 (psi s (closureCounterIndex s) 0) (indexIter s 0 n) := by
      intro n
      induction n with
      | zero => exact C_zero s _ _
      | succ n ih => exact C_index s _ _ 0 _ (C_zero s _ _) ih
    apply (sup_le_iff _ _).mpr
    intro n
    have hn := indexIter_lt_sup s 0 n
    rw [heq] at hn
    exact Or.inl (psi_closed s _ _ _ (hc n) (lt_trans _ _ _ hn (base_lt_closureCounterIndex s)))

theorem closureCounterValue_mem (s : Supply) :
    C s (succ 0) omega (psi s (closureCounterIndex s) 0) := by
  rw [closureCounterValue_eq_base]
  exact C_collapse s (succ 0) omega (I s (succ 0) 0) 0 (lt_succ_self 0)
    (Or.inl ⟨succ 0, rfl⟩) (first_inaccessible_mem_C s _ _ (lt_succ_self 0)) (C_zero s _ _)

theorem closureCounterUpper_not_mem (s : Supply) : ¬ C s (succ 0) omega (closureCounterUpper s) := by
  intro hC
  have hsmall : omega < closureCounterUpper s := lt_trans _ _ _ (first_regular s).1
    (first_lt_psi_above s _ _ (first_lt_first_inaccessible s))
  have hC' := C_mono_seed s (succ 0) omega (closureCounterUpper s) (Or.inl hsmall) _ hC
  exact lt_irrefl _ (psi_closed s (I s (succ 0) 0) (succ 0) _ hC'
    (psi_lt s _ _ (inaccessible_regular (first_inaccessible s (succ 0)))))

theorem closureCounterIndex_not_mem (s : Supply) : ¬ C s (succ 0) omega (closureCounterIndex s) := by
  intro hC
  have hreg := regularIndex_regular s _ (closureCounterIndex_regular s)
  have hp : 0 < closureCounterIndex s := regular_pos hreg
  have hb := regular_succ_lt hreg (closureCounterUpper_lt_index s)
  obtain ⟨_, hbC⟩ := C_normal_index_parameters s (succ 0) omega 0 (succ (closureCounterUpper s)) hp hb hC
  exact closureCounterUpper_not_mem s (C_predecessor s (succ 0) omega _ hbC)

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem closureCounterUpper_represented (s : OCF.Denis.Supply) :
    Represented s (OCF.Denis.closureCounterUpper s) := by
  apply represented_psi_of_mem s _ _ ⟨I1, I1_isNormal s, denote_I1 s⟩
    ⟨one, one_isNormal s, denote_one s⟩ (Or.inl ⟨succ 0, rfl⟩)
  apply OCF.Denis.C_seed
  exact OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.finite_lt_omega 1)
    (OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.first_regular s).1
      (OCF.Denis.first_lt_psi_above s _ _ (OCF.Denis.first_lt_first_inaccessible s)))

theorem closureCounterIndex_represented (s : OCF.Denis.Supply) :
    Represented s (OCF.Denis.closureCounterIndex s) :=
  represented_I s 0 _ ⟨.zero, .zero, rfl⟩
    (represented_succ s _ (closureCounterUpper_represented s))

/-- Both the index and the collapse are normal represented terms, but
membership of the value in a closure does not give membership of its
displayed index. Normality alone cannot justify that inversion rule. -/
theorem normal_closure_not_index_hereditary (s : OCF.Denis.Supply) :
    ∃ k : Term, IsNormal s k ∧ IsNormal s (.psi k .zero) ∧
      OCF.Denis.C s (succ 0) OCF.Denis.omega (denote s (.psi k .zero)) ∧
      ¬ OCF.Denis.C s (succ 0) OCF.Denis.omega (denote s k) := by
  obtain ⟨k, hk, heq⟩ := closureCounterIndex_represented s
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · apply IsNormal.collapse hk .zero
    · rw [heq]; exact OCF.Denis.closureCounterIndex_regular s
    · exact OCF.Denis.C_zero s _ _
  · change OCF.Denis.C s (succ 0) OCF.Denis.omega (OCF.Denis.psi s (denote s k) 0)
    rw [heq]
    exact OCF.Denis.closureCounterValue_mem s
  · rw [heq]
    exact OCF.Denis.closureCounterIndex_not_mem s

/-- The displayed index can be replaced while preserving the ordinal
value; the counterexample does not remove that value from the system. -/
theorem closureCounter_normalization (s : OCF.Denis.Supply) (k : Term)
    (hk : denote s k = OCF.Denis.closureCounterIndex s) :
    denote s (.psi k .zero) = denote s cardFixed := by
  change OCF.Denis.psi s (denote s k) 0 = _
  rw [hk, OCF.Denis.closureCounterValue_eq_base, denote_cardFixed]

theorem revised_closureCounter_fundamentalSequence (s : OCF.Denis.Supply) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.closureCounterIndex s) 0)
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.closureCounterIndex s) 0)) := by
  rw [OCF.Denis.closureCounterValue_eq_base]
  exact revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos
      (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ 0, rfl⟩)))) (cardFixed_dense s)

end
end T.Correspondence.Denis.Covering
