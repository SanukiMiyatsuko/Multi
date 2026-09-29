import Multi.term3.Denis.NormalInterpolation

/-! Diagonal sequences for normal regular I indices with arbitrary
represented parameters below the first regular index. The parameters
are not restricted to finite ordinals. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem diagonalSeed_of_small_parameters (s : OCF.Denis.Supply) (p b : OCF.Denis.O)
    (hp : Represented s p) (hb : Represented s b)
    (hreg : OCF.Denis.RegularIndex s (OCF.Denis.I s p b))
    (hpb : p < OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b))
    (hbb : b < OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b)) :
    ∃ c, Represented s c ∧ OCF.Denis.DiagonalSeed s (OCF.Denis.I s p b) c := by
  classical
  have hx : Represented s (maxOrdinal p b) := by
    unfold maxOrdinal
    split
    · exact hb
    · exact hp
  have hxbd : maxOrdinal p b < OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b) := by
    unfold maxOrdinal
    split
    · exact hbb
    · exact hpb
  obtain ⟨c, hc, hcr, hxc, harg⟩ := represented_interpolation s (OCF.Denis.I s p b)
    (maxOrdinal p b) (OCF.Denis.regularIndex_regular s _ hreg) hx hxbd
  refine ⟨c, hc, hcr, harg, ?_⟩
  exact OCF.Denis.C_index s _ _ p b
    (OCF.Denis.C_seed s _ _ p (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_left p b) hxc))
    (OCF.Denis.C_seed s _ _ b (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_right p b) hxc))

theorem psi_first_countable_regular_index_dense (s : OCF.Denis.Supply) (p b : OCF.Denis.O)
    (hp : Represented s p) (hb : Represented s b)
    (hpfirst : p < OCF.Denis.I s 0 0) (hbfirst : b < OCF.Denis.I s 0 0)
    (hreg : OCF.Denis.RegularIndex s (OCF.Denis.I s p b))
    (harg : OCF.Denis.C s (OCF.Denis.I s p b)
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b)) (OCF.Denis.I s p b)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b)) := by
  have hlow := OCF.Denis.I_lower_bound s p b
  have hpI := OCF.Ordinal.lt_of_lt_of_le hpfirst hlow
  have hbI := OCF.Ordinal.lt_of_lt_of_le hbfirst hlow
  obtain ⟨hpC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ p b hpI hbI harg
  have hpb := OCF.Denis.psi_closed s _ _ p hpC hpfirst
  have hbb := OCF.Denis.psi_closed s _ _ b hbC hbfirst
  rcases hlow with hlarge | heq
  · obtain ⟨c, hc, hseed⟩ := diagonalSeed_of_small_parameters s p b hp hb hreg hpb hbb
    exact seeded_diagonal_dense s _ c (represented_I s p b hp hb) hc hreg hlarge hseed
  · rw [← heq]
    exact epsilon_dense s

theorem revised_psi_first_countable_regular_index_fundamentalSequence
    (s : OCF.Denis.Supply) (p b : OCF.Denis.O) (hp : Represented s p) (hb : Represented s b)
    (hpfirst : p < OCF.Denis.I s 0 0) (hbfirst : b < OCF.Denis.I s 0 0)
    (hreg : OCF.Denis.RegularIndex s (OCF.Denis.I s p b))
    (harg : OCF.Denis.C s (OCF.Denis.I s p b)
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b)) (OCF.Denis.I s p b)) :
    OCF.Denis.FundamentalSequence
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s p b))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (psi_first_countable_regular_index_dense s p b hp hb hpfirst hbfirst hreg harg)

end
end T.Correspondence.Denis.Covering
