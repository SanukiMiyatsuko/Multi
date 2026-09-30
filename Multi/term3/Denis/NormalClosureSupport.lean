import Multi.term3.Denis.ClosureStageApproximation

/-! A finite support cutoff for any normal syntax tree. Subterms already
below the seed are leaves; other collapses require a cutoff above their
argument. This gives a sufficient closure and earlier-stage criterion
without bounding an inner collapse argument by its own index. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def supportCutoff (s : OCF.Denis.Supply) (beta : OCF.Denis.O) (t : Term) : OCF.Denis.O :=
  if denote s t < beta then 0 else
    match t with
    | .zero => 0
    | .add p b | .I p b => maxOrdinal (supportCutoff s beta p) (supportCutoff s beta b)
    | .psi k a => maxOrdinal (maxOrdinal (supportCutoff s beta k) (supportCutoff s beta a)) (succ (denote s a))

theorem maxOrdinal_represented (s : OCF.Denis.Supply) (x y : OCF.Denis.O)
    (hx : Represented s x) (hy : Represented s y) : Represented s (maxOrdinal x y) := by
  unfold maxOrdinal
  split <;> assumption

theorem supportCutoff_represented (s : OCF.Denis.Supply) (beta : OCF.Denis.O) (t : Term)
    (ht : IsNormal s t) : Represented s (supportCutoff s beta t) := by
  induction ht with
  | zero =>
    unfold supportCutoff
    split <;> exact ⟨.zero, .zero, rfl⟩
  | @sum p b hp hb _ _ _ _ ihp ihb | @index p b hp hb _ _ ihp ihb =>
    unfold supportCutoff
    split
    · exact ⟨.zero, .zero, rfl⟩
    · exact maxOrdinal_represented s _ _ ihp ihb
  | @collapse k a hk ha hreg harg ihk iha =>
    unfold supportCutoff
    split
    · exact ⟨.zero, .zero, rfl⟩
    · exact maxOrdinal_represented s _ _ (maxOrdinal_represented s _ _ ihk iha)
        (represented_succ s _ ⟨a, ha, rfl⟩)

theorem C_of_supportCutoff_le (s : OCF.Denis.Supply) (cutoff beta : OCF.Denis.O) (t : Term)
    (ht : IsNormal s t) (hbound : supportCutoff s beta t ≤ cutoff) :
    OCF.Denis.C s cutoff beta (denote s t) := by
  induction ht with
  | zero => exact OCF.Denis.C_zero s cutoff beta
  | @sum p b hp hb _ _ _ _ ihp ihb =>
    by_cases hseed : denote s (.add p b) < beta
    · exact OCF.Denis.C_seed s cutoff beta _ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      exact OCF.Denis.C_add s cutoff beta _ _
        (ihp (OCF.Ordinal.le_trans (le_maxOrdinal_left _ _) hbound))
        (ihb (OCF.Ordinal.le_trans (le_maxOrdinal_right _ _) hbound))
  | @index r b hr hb _ _ ihr ihb =>
    by_cases hseed : denote s (.I r b) < beta
    · exact OCF.Denis.C_seed s cutoff beta _ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      exact OCF.Denis.C_index s cutoff beta _ _
        (ihr (OCF.Ordinal.le_trans (le_maxOrdinal_left _ _) hbound))
        (ihb (OCF.Ordinal.le_trans (le_maxOrdinal_right _ _) hbound))
  | @collapse k a hk ha hreg harg ihk iha =>
    by_cases hseed : denote s (.psi k a) < beta
    · exact OCF.Denis.C_seed s cutoff beta _ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      have hp := OCF.Ordinal.le_trans (le_maxOrdinal_left _ _) hbound
      have haCut := (succ_le_iff_lt _ _).mp (OCF.Ordinal.le_trans (le_maxOrdinal_right _ _) hbound)
      exact OCF.Denis.C_collapse s cutoff beta _ _ haCut hreg
        (ihk (OCF.Ordinal.le_trans (le_maxOrdinal_left _ _) hp))
        (iha (OCF.Ordinal.le_trans (le_maxOrdinal_right _ _) hp))

theorem representedClosureStage_of_supportCutoff_lt (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a)
    (t : Term) (ht : IsNormal s t) (hbound : supportCutoff s (OCF.Denis.psi s k a) t < a) :
    RepresentedClosureStage s k a (denote s t) := by
  induction ht with
  | zero => exact ⟨0, ⟨.zero, .zero, rfl⟩, (zero_lt_iff_ne_zero a).mpr ha.1, OCF.Denis.C_zero s _ _⟩
  | @sum p b hp hb hpp hpv hbpos hhead ihp ihb =>
    by_cases hseed : denote s (.add p b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha ⟨_, .sum hp hb hpp hpv hbpos hhead, rfl⟩ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      obtain ⟨c, hc, hca, hcp, hcb⟩ := representedClosureStage_pair s k a _ _
        (ihp (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_left _ _) hbound))
        (ihb (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_right _ _) hbound))
      exact ⟨c, hc, hca, OCF.Denis.C_add s c _ _ _ hcp hcb⟩
  | @index r b hr hb hrl hbl ihr ihb =>
    by_cases hseed : denote s (.I r b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha ⟨_, .index hr hb hrl hbl, rfl⟩ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      obtain ⟨c, hc, hca, hcr, hcb⟩ := representedClosureStage_pair s k a _ _
        (ihr (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_left _ _) hbound))
        (ihb (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_right _ _) hbound))
      exact ⟨c, hc, hca, OCF.Denis.C_index s c _ _ _ hcr hcb⟩
  | @collapse l b hl hb hreg harg ihl ihb =>
    by_cases hseed : denote s (.psi l b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha ⟨_, .collapse hl hb hreg harg, rfl⟩ hseed
    · simp only [supportCutoff, if_neg hseed] at hbound
      have hp := OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_left _ _) hbound
      have hbCut := OCF.Ordinal.lt_trans _ _ _ (lt_succ_self (denote s b))
        (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_right _ _) hbound)
      exact representedClosureStage_collapse s k a _ _ ha hreg ⟨b, hb, rfl⟩ hbCut
        (ihl (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_left _ _) hp))
        (ihb (OCF.Ordinal.lt_of_le_of_lt (le_maxOrdinal_right _ _) hp))

end
end T.Correspondence.Denis.Covering
