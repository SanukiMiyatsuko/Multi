import Multi.term3.Denis.ClosureCounterexample

/-! Value-preserving normalization on whole zero-argument plateau intervals.
This works even when the displayed collapse index is not in the defining
closure. The replacement index is proved to be in that closure. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem rank_lt_psi_of_first_le (s : Supply) (r k : O) (hr : RankBounded s r)
    (hk : I s r 0 ≤ k) : r < psi s k 0 := by
  have hkpos := lt_of_lt_of_le
    (regular_pos (regularIndex_regular s _ (Or.inl ⟨r, rfl⟩))) hk
  let p := psi s k 0
  have hp : 0 < p := psi_pos s k 0 hkpos
  have impossible (hpr : p ≤ r) : False := by
    have ht : ∀ n, rankTower s n < p := by
      intro n
      induction n with
      | zero => exact hp
      | succ n ih =>
        have hnr := lt_of_lt_of_le ih hpr
        have hI : I s (rankTower s n) 0 < I s r 0 := by
          rw [I_zero, I_zero]
          exact first_rank_strict s hnr
        exact psi_closed s k 0 _
          (C_index s 0 p _ 0 (C_seed s 0 p _ ih) (C_zero s 0 p))
          (lt_of_lt_of_le hI hk)
    obtain ⟨n, hn⟩ := hr
    exact lt_irrefl _ (lt_of_lt_of_le (lt_trans _ _ _ hn (ht n)) hpr)
  rcases lt_total r p with h | h | h
  · exact h
  · exact False.elim (impossible (Or.inr h.symm))
  · exact False.elim (impossible (Or.inl h))

theorem psi_zero_plateau (s : Supply) (r k : O)
    (hlower : psi s (I s (succ r) 0) 0 < k) (hupper : k ≤ I s (succ r) 0) :
    psi s k 0 = psi s (I s (succ r) 0) 0 := by
  exact psi_index_plateau s k _ 0 (Or.inl hlower) hupper

theorem successor_rank_index_mem (s : Supply) (r : O) (hr : RankBounded s r) :
    C s 0 (psi s (I s (succ r) 0) 0) (I s (succ r) 0) := by
  have hf := bounded_rank_zero_fundamentalSequence s r hr
  have hsmall := succ_lt_limit hf.isLimit (rank_lt_psi_first_succ_rank s r hr)
  exact C_index s 0 _ (succ r) 0 (C_seed s 0 _ _ hsmall) (C_zero s 0 _)

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

def successorRankZeroTerm (r : Term) : Term := .psi (.I (succTerm r) .zero) .zero

theorem denote_successorRankZeroTerm (s : OCF.Denis.Supply) (r : Term) :
    denote s (successorRankZeroTerm r) = OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) 0 := by
  change OCF.Denis.psi s (OCF.Denis.I s (denote s (succTerm r)) 0) 0 = _
  rw [denote_succTerm]

theorem successorRankZeroTerm_normal (s : OCF.Denis.Supply) (r : Term) (hr : IsNormal s r) :
    IsNormal s (successorRankZeroTerm r) := by
  have hs := succTerm_normal s r hr
  have hbound := normal_rankBounded s (succTerm r) hs
  have hlt := OCF.Denis.rank_lt_first_of_bounded s (denote s (succTerm r)) hbound
  rw [← OCF.Denis.I_zero] at hlt
  apply IsNormal.collapse (IsNormal.index hs .zero hlt
    (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨denote s (succTerm r), rfl⟩)))) .zero
  · exact Or.inl ⟨denote s (succTerm r), rfl⟩
  · exact OCF.Denis.C_zero s _ _

theorem zero_plateau_normalization (s : OCF.Denis.Supply) (r k : Term) (hr : IsNormal s r)
    (hlower : OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) 0 < denote s k)
    (hupper : denote s k ≤ OCF.Denis.I s (succ (denote s r)) 0) :
    IsNormal s (successorRankZeroTerm r) ∧ denote s (.psi k .zero) = denote s (successorRankZeroTerm r) := by
  refine ⟨successorRankZeroTerm_normal s r hr, ?_⟩
  rw [denote_successorRankZeroTerm]
  exact OCF.Denis.psi_zero_plateau s (denote s r) (denote s k) hlower hupper

theorem zero_plateau_dense (s : OCF.Denis.Supply) (r k : OCF.Denis.O) (hr : Represented s r)
    (hlower : OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0 < k)
    (hupper : k ≤ OCF.Denis.I s (succ r) 0) : DenseBelow s (OCF.Denis.psi s k 0) := by
  obtain ⟨rt, hrt, rfl⟩ := hr
  rw [OCF.Denis.psi_zero_plateau s _ _ hlower hupper]
  exact successor_rank_zero_dense s _ ⟨rt, hrt, rfl⟩

theorem revised_zero_plateau_fundamentalSequence (s : OCF.Denis.Supply) (r k : OCF.Denis.O)
    (hr : Represented s r) (hlower : OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0 < k)
    (hupper : k ≤ OCF.Denis.I s (succ r) 0) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s k 0) (revisedValue s (OCF.Denis.psi s k 0)) := by
  obtain ⟨rt, hrt, rfl⟩ := hr
  rw [OCF.Denis.psi_zero_plateau s _ _ hlower hupper]
  exact revised_successor_rank_zero_fundamentalSequence s _ ⟨rt, hrt, rfl⟩

end
end T.Correspondence.Denis.Covering
