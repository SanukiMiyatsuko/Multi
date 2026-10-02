import Multi.term3.Denis.UniformStageRank

/-! The large limit step, and covering sequences for all normal terms.

Every normal term satisfies the uniform stage bound, by induction on its
size: sums and `I` at limits pass to their tails, regular values are the
base case, and a collapse either has a smaller normal presentation, a
limit argument, or a zero or successor argument whose index has a limit
rank. Applied to the argument of an isolated large limit collapse, the
uniform bound is `IsolatedStageBound`, so the generic diagonal gives its
covering sequence. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem ustage_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    OCF.Denis.UStage s (denote s t) := by
  classical
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    cases ht with
    | zero => exact OCF.Denis.ustage_zero s
    | @index r b hr hb hrl hbl =>
      by_cases hb0 : denote s b = 0
      · apply OCF.Denis.ustage_regular
        change OCF.Denis.RegularIndex s (OCF.Denis.I s (denote s r) (denote s b))
        exact Or.inl ⟨denote s r, by rw [hb0]⟩
      · by_cases hbs : ∃ c, denote s b = succ c
        · obtain ⟨c, hc⟩ := hbs
          apply OCF.Denis.ustage_regular
          change OCF.Denis.RegularIndex s (OCF.Denis.I s (denote s r) (denote s b))
          exact Or.inr ⟨denote s r, c, by rw [hc]⟩
        · exact OCF.Denis.ustage_I_limit s _ _ ⟨hb0, hbs⟩ hrl hbl
            (ih b (by change sizeOf b < sizeOf (Term.I r b); simp; omega) hb)
    | @sum p q hp hq hpp hprin hqpos hhead =>
      have hn : IsNormal s (.add p q) := .sum hp hq hpp hprin hqpos hhead
      exact OCF.Denis.ustage_sum s _ _ hqpos
        (fun A' B' hC => C_normal_sum_head s A' B' p q hn hC)
        (ih q (by change sizeOf q < sizeOf (Term.add p q); simp; omega) hq)
    | @collapse k a hk ha hreg harg =>
      have hn : IsNormal s (.psi k a) := .collapse hk ha hreg harg
      by_cases hK : OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a))
          (denote s k)
      · obtain ⟨r, z, rfl⟩ := CollapseNormalization.normal_regular_is_index s k hk
          (OCF.Denis.regularIndex_regular s _ hreg)
        cases hk with
        | index hr hz hrl hzl =>
          have hp : OCF.Denis.ProperCollapse s (denote s (.I r z)) (denote s a) := ⟨hreg, hK, harg⟩
          have hrsize : sizeOf r < sizeOf (Term.psi (.I r z) a) := by simp; omega
          by_cases ha0 : denote s a = 0
          · exact OCF.Denis.ustage_psi_rank s _ _ _ _ hp (Or.inl ha0) rfl hrl hzl
              (ih r hrsize hr)
          · by_cases has : ∃ c, denote s a = succ c
            · exact OCF.Denis.ustage_psi_rank s _ _ _ _ hp (Or.inr has) rfl hrl hzl
                (ih r hrsize hr)
            · exact OCF.Denis.ustage_psi_limit s _ _ _ _ hp ⟨ha0, has⟩ rfl hrl hzl
                (ih a (by change sizeOf a < sizeOf (Term.psi (.I r z) a); simp; omega) ha)
      · obtain ⟨l, b, hnb, heq, hsize⟩ :=
          CollapseNormalization.smaller_of_index_not_mem s k a hn hK
        rw [← heq]
        exact ih _ hsize hnb

/-- The uniform bound at an isolated argument is the stage bound of the
diagonal construction. -/
theorem isolatedStageBound_of_ustage (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkrep : Represented s k) (harep : Represented s a)
    (haD : OCF.Denis.C s a (OCF.Denis.psi s k a) a)
    (hkD : OCF.Denis.C s a (OCF.Denis.psi s k a) k) (ha : OCF.Denis.IsLimit a)
    (hiso : ∃ c, c < a ∧ OCF.Denis.psi s k c = OCF.Denis.psi s k a)
    (hU : OCF.Denis.UStage s a) : IsolatedStageBound s k a := by
  intro y hyrep hyD hya
  obtain ⟨c, hca, hc⟩ := hiso
  obtain ⟨_, _, hgap⟩ := OCF.Denis.psi_proper_plateau s k a k c hk hk hkD haD hc
  have hiso' : OCF.Denis.IsoIn s a (OCF.Denis.psi s k a) a := ⟨ha, c, hca, hgap⟩
  obtain ⟨w, hwa, hwb, hwZ⟩ := hU k a y hk haD hiso' hya
  have hwrep : Represented s w := by
    obtain ⟨A1, h1⟩ := (represented_iff_C_zero s a).mp harep
    obtain ⟨A2, h2⟩ := (represented_iff_C_zero s y).mp hyrep
    obtain ⟨A3, h3⟩ := (represented_iff_C_zero s k).mp hkrep
    have hB1 : A1 ≤ A1 + A2 + A3 + succ y :=
      OCF.Ordinal.le_trans (OCF.Ordinal.le_trans (le_add A1 A2) (le_add _ A3)) (le_add _ _)
    have hB2 : A2 ≤ A1 + A2 + A3 + succ y :=
      OCF.Ordinal.le_trans (OCF.Ordinal.le_trans (right_le_add A1 A2) (le_add _ A3)) (le_add _ _)
    have hB3 : A3 ≤ A1 + A2 + A3 + succ y :=
      OCF.Ordinal.le_trans (right_le_add _ A3) (le_add _ _)
    have hyB : y < A1 + A2 + A3 + succ y :=
      OCF.Ordinal.lt_of_lt_of_le (lt_succ_self y) (right_le_add _ _)
    exact represented_of_C_zero s _ w (hwZ _ 0 (OCF.Denis.C_mono_argument s A1 _ 0 hB1 a h1)
      (OCF.Denis.C_mono_argument s A2 _ 0 hB2 y h2) (OCF.Denis.C_mono_argument s A3 _ 0 hB3 k h3)
      hyB)
  have hwD := hwZ a _ haD hyD hkD hya
  refine ⟨maxOrdinal y w, ?_, ?_, ?_,
    le_maxOrdinal_left y w, fun b hb hba =>
      OCF.Ordinal.lt_of_lt_of_le (hwb b hb hba) (le_maxOrdinal_right y w)⟩
  · unfold maxOrdinal
    split <;> assumption
  · unfold maxOrdinal
    split <;> assumption
  · unfold maxOrdinal
    split <;> assumption

/-- The isolated large limit step holds. -/
theorem isolatedLargeLimitStep_holds (s : OCF.Denis.Supply) : IsolatedLargeLimitStep s := by
  apply isolatedLargeLimitStep_of_stageBound
  intro k a hn ha _ _ hK hiso
  have hk : IsNormal s k := by cases hn; assumption
  have hanorm : IsNormal s a := by cases hn; assumption
  have hreg : OCF.Denis.RegularIndex s (denote s k) := by cases hn; assumption
  have harg : OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a))
      (denote s a) := by cases hn; assumption
  exact isolatedStageBound_of_ustage s _ _ hreg ⟨k, hk, rfl⟩ ⟨a, hanorm, rfl⟩ harg hK ha hiso
    (ustage_normal s a hanorm)

/-- The large limit step `LargeLimitCoveringStep` holds. -/
theorem largeLimitCoveringStep_holds (s : OCF.Denis.Supply) : LargeLimitCoveringStep s :=
  largeLimitCoveringStep_of_isolated s (isolatedLargeLimitStep_holds s)

/-- Every normal term has a covering fundamental sequence of the minimal
length, with normal values at normal indices. -/
theorem normal_hasCoveringSequence (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    HasCoveringSequence s (denote s t) :=
  normal_hasCoveringSequence_of_isolated s (isolatedLargeLimitStep_holds s) t ht

/-- Every normal term has a normal fundamental sequence of the minimal
length. -/
theorem normal_hasNormalSequence (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    HasNormalSequence s (denote s t) :=
  (normal_hasCoveringSequence s t ht).to_normal

/-- The earlier formulations of the remaining limit step also hold. -/
theorem properLimitStep_holds (s : OCF.Denis.Supply) : ProperLimitStep s :=
  (properLimitStep_iff_all_normal s).mpr (normal_hasNormalSequence s)

theorem properRemainingLimitStep_holds (s : OCF.Denis.Supply) : ProperRemainingLimitStep s :=
  (properRemainingLimitStep_iff_all_normal s).mpr (normal_hasNormalSequence s)

/-- At countable cofinality the normal values are dense below the actual
ordinal. -/
theorem normal_dense_of_cofinality_omega (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (ha : OCF.Denis.IsLimit (denote s t))
    (hcof : OCF.Denis.cofinality (denote s t) ha = OCF.Denis.omega) :
    DenseBelow s (denote s t) := by
  obtain ⟨_, f, hf⟩ := normal_hasCoveringSequence s t ht ha
  rw [hcof] at hf
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hf.normalSequence.fundamental.cofinal x hx
  obtain ⟨n, rfl⟩ := (OCF.Denis.lt_omega_iff i).mp hi
  exact ⟨f (OCF.Denis.finite n), hf.normalSequence.normal _ hi (finite_represented s n), hxi,
    hf.normalSequence.fundamental.below _ hi⟩

/-- At countable cofinality the repaired natural-number expansion is
cofinal in the actual ordinal. -/
theorem normal_revised_cofinal_of_cofinality_omega (s : OCF.Denis.Supply) (t : Term)
    (ht : IsNormal s t) (ha : OCF.Denis.IsLimit (denote s t))
    (hcof : OCF.Denis.cofinality (denote s t) ha = OCF.Denis.omega) :
    ∀ x, x < denote s t → ∃ n, x < revisedValue s (denote s t) n :=
  (dense_iff_revised_cofinal s _ ((zero_lt_iff_ne_zero _).mpr ha.1)).mp
    (normal_dense_of_cofinality_omega s t ht ha hcof)

end
end T.Correspondence.Denis.Covering
