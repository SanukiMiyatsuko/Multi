import Multi.term3.Denis.ZeroPlateau

/-! Eliminate nested lower-rank indices without changing the collapse
value. The inner collapse argument may be an arbitrary ordinal. The
syntactic replacement preserves normality and strictly reduces size. -/

namespace OCF.Denis
open Ordinal

theorem psi_nested_index_eq (s : Supply) (q r b t a : O)
    (hqr : q < r) (hreg : RegularIndex s (I s r b)) (hat : a ≤ t) :
    psi s (I s q (succ (psi s (I s r b) t))) a = psi s (I s r b) a := by
  have hinner := psi_lt s (I s r b) t (regularIndex_regular s _ hreg)
  have hindex := I_lower_rank_closed s q r b (succ (psi s (I s r b) t)) hqr
    (regular_succ_lt (regularIndex_regular s _ hreg) hinner)
  apply psi_index_plateau s _ _ a
  · exact le_trans (psi_mono s (I s r b) a t hat)
      (Or.inl (lt_of_lt_of_le (lt_succ_self _) (index_le_I s q _)))
  · exact Or.inl hindex

theorem psi_nested_successor_rank_zero (s : Supply) (q r t : O) (hqr : q ≤ r) :
    psi s (I s q (succ (psi s (I s (succ r) 0) t))) 0 = psi s (I s (succ r) 0) 0 :=
  psi_nested_index_eq s q (succ r) 0 t 0 ((lt_succ_iff_le q r).mpr hqr)
    (Or.inl ⟨succ r, rfl⟩) (zero_le t)

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

def nestedCollapse (q r b t a : Term) : Term := .psi (.I q (succTerm (.psi (.I r b) t))) a

theorem nestedCollapse_value (s : OCF.Denis.Supply) (q r b t a : Term)
    (hqr : denote s q < denote s r) (hreg : OCF.Denis.RegularIndex s (denote s (.I r b)))
    (hat : denote s a ≤ denote s t) :
    denote s (nestedCollapse q r b t a) = denote s (.psi (.I r b) a) := by
  change OCF.Denis.psi s (OCF.Denis.I s (denote s q) (denote s (succTerm (.psi (.I r b) t)))) (denote s a) = _
  rw [denote_succTerm]
  exact OCF.Denis.psi_nested_index_eq s _ _ _ _ _ hqr hreg hat

theorem nestedCollapse_replacement_normal (s : OCF.Denis.Supply) (q r b t a : Term)
    (h : IsNormal s (nestedCollapse q r b t a))
    (hqr : denote s q < denote s r) (hat : denote s a ≤ denote s t) :
    IsNormal s (.psi (.I r b) a) ∧
      denote s (nestedCollapse q r b t a) = denote s (.psi (.I r b) a) := by
  cases h with
  | collapse hindex ha _ harg =>
    cases hindex with
    | index hq hs _ _ =>
      change IsNormal s (.add (.psi (.I r b) t) one) at hs
      cases hs with
      | sum hinner _ _ _ _ _ =>
        cases hinner with
        | collapse hbase _ hreg _ =>
          have heq := nestedCollapse_value s q r b t a hqr hreg hat
          refine ⟨IsNormal.collapse hbase ha hreg ?_, heq⟩
          change OCF.Denis.C s (denote s a) (denote s (nestedCollapse q r b t a)) (denote s a) at harg
          rw [heq] at harg
          exact harg

theorem nestedCollapse_replacement_smaller (q r b t a : Term) :
    sizeOf (Term.psi (.I r b) a) < sizeOf (nestedCollapse q r b t a) := by
  simp [nestedCollapse, succTerm]
  omega

theorem nestedCollapse_revised_agrees (s : OCF.Denis.Supply) (q r b t a : Term)
    (h : IsNormal s (nestedCollapse q r b t a))
    (hqr : denote s q < denote s r) (hat : denote s a ≤ denote s t) (n : Nat) :
    revisedValue s (denote s (nestedCollapse q r b t a)) n =
      revisedValue s (denote s (.psi (.I r b) a)) n := by
  rw [(nestedCollapse_replacement_normal s q r b t a h hqr hat).2]

theorem nested_successor_rank_zero_dense (s : OCF.Denis.Supply) (q r t : OCF.Denis.O)
    (hr : Represented s r) (hqr : q ≤ r) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s q
      (succ (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) t))) 0) := by
  rw [OCF.Denis.psi_nested_successor_rank_zero s q r t hqr]
  exact successor_rank_zero_dense s r hr

theorem revised_nested_successor_rank_zero_fundamentalSequence (s : OCF.Denis.Supply)
    (q r t : OCF.Denis.O) (hr : Represented s r) (hqr : q ≤ r) :
    OCF.Denis.FundamentalSequence
      (OCF.Denis.psi s (OCF.Denis.I s q (succ (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) t))) 0)
      (revisedValue s (OCF.Denis.psi s
        (OCF.Denis.I s q (succ (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) t))) 0)) := by
  rw [OCF.Denis.psi_nested_successor_rank_zero s q r t hqr]
  exact revised_successor_rank_zero_fundamentalSequence s r hr

end
end T.Correspondence.Denis.Covering
