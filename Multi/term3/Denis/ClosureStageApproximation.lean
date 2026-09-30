import Multi.term3.Denis.CompositeSequenceCoverage

/-! Closure support at represented earlier stages of a limit collapse.
The outer index is arbitrary and the limit cutoff need not be regular.
The proved tree family permits nested proper collapses at arbitrary regular indices. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

/-- A represented earlier cutoff supports `x` in the outer collapse's
closure. No self-membership of the cutoff is required. -/
def RepresentedClosureStage (s : OCF.Denis.Supply) (k a x : OCF.Denis.O) : Prop :=
  ∃ c, Represented s c ∧ c < a ∧ OCF.Denis.C s c (OCF.Denis.psi s k c) x

theorem closure_stage_mono (s : OCF.Denis.Supply) (k c d x : OCF.Denis.O)
    (hcd : c ≤ d) (hx : OCF.Denis.C s c (OCF.Denis.psi s k c) x) :
    OCF.Denis.C s d (OCF.Denis.psi s k d) x :=
  OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s k c d hcd) x
    (OCF.Denis.C_mono_argument s c d _ hcd x hx)

theorem representedClosureStage_pair (s : OCF.Denis.Supply) (k a x y : OCF.Denis.O)
    (hx : RepresentedClosureStage s k a x) (hy : RepresentedClosureStage s k a y) :
    ∃ c, Represented s c ∧ c < a ∧ OCF.Denis.C s c (OCF.Denis.psi s k c) x ∧
      OCF.Denis.C s c (OCF.Denis.psi s k c) y := by
  obtain ⟨c, hc, hca, hxc⟩ := hx
  obtain ⟨d, hd, hda, hyd⟩ := hy
  rcases OCF.Ordinal.lt_total c d with h | h | h
  · exact ⟨d, hd, hda, closure_stage_mono s k c d x (Or.inl h) hxc, hyd⟩
  · exact ⟨d, hd, hda, h ▸ hxc, hyd⟩
  · exact ⟨c, hc, hca, hxc, closure_stage_mono s k d c y (Or.inl h) hyd⟩

theorem representedClosureStage_of_lt (s : OCF.Denis.Supply) (k a x : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a)
    (hx : Represented s x) (hxa : x < OCF.Denis.psi s k a) :
    RepresentedClosureStage s k a x := by
  obtain ⟨c, hc, hca, hxc⟩ := represented_limit_collapse_interpolation s k a x hk ha hx hxa
  exact ⟨c, hc, hca, OCF.Denis.C_seed s _ _ _ hxc⟩

theorem representedClosureStage_successorRankCollapse (s : OCF.Denis.Supply) (k a r b : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hb : Represented s b) (hba : b < a)
    (hrC : RepresentedClosureStage s k a r) (hbC : RepresentedClosureStage s k a b) :
    RepresentedClosureStage s k a (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) b) := by
  obtain ⟨c, hc, hca, hcr, hcb⟩ := representedClosureStage_pair s k a r b hrC hbC
  obtain ⟨d, hd, hda, hcd, hbd⟩ := combine_represented_stages s a c b (fun x => x) (fun _ _ h => h)
    ⟨succ c, represented_succ s c hc, OCF.Denis.succ_lt_limit ha hca, lt_succ_self c⟩
    ⟨succ b, represented_succ s b hb, OCF.Denis.succ_lt_limit ha hba, lt_succ_self b⟩
  have hdpos := OCF.Ordinal.lt_of_le_of_lt (zero_le b) hbd
  have hsucc := OCF.Denis.C_add s d (OCF.Denis.psi s k d) r (succ 0)
    (closure_stage_mono s k c d r (Or.inl hcd) hcr) (OCF.Denis.C_finite s d _ hdpos 1)
  rw [add_succ, add_zero] at hsucc
  exact ⟨d, hd, hda, OCF.Denis.C_collapse s d _ _ b hbd (Or.inl ⟨succ r, rfl⟩)
    (OCF.Denis.C_index s d _ (succ r) 0 hsucc (OCF.Denis.C_zero s d _))
    (closure_stage_mono s k c d b (Or.inl hcd) hcb)⟩

theorem representedClosureStage_collapse (s : OCF.Denis.Supply) (k a l b : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hl : OCF.Denis.RegularIndex s l)
    (hb : Represented s b) (hba : b < a)
    (hlC : RepresentedClosureStage s k a l) (hbC : RepresentedClosureStage s k a b) :
    RepresentedClosureStage s k a (OCF.Denis.psi s l b) := by
  obtain ⟨c, hc, hca, hcl, hcb⟩ := representedClosureStage_pair s k a l b hlC hbC
  obtain ⟨d, hd, hda, hcd, hbd⟩ := combine_represented_stages s a c b (fun x => x) (fun _ _ h => h)
    ⟨succ c, represented_succ s c hc, OCF.Denis.succ_lt_limit ha hca, lt_succ_self c⟩
    ⟨succ b, represented_succ s b hb, OCF.Denis.succ_lt_limit ha hba, lt_succ_self b⟩
  exact ⟨d, hd, hda, OCF.Denis.C_collapse s d _ l b hbd hl
    (closure_stage_mono s k c d l (Or.inl hcd) hcl) (closure_stage_mono s k c d b (Or.inl hcd) hcb)⟩

theorem CollapseTree.representedClosureStage {s : OCF.Denis.Supply} {t : Term} (ht : CollapseTree s t)
    (k a : OCF.Denis.O) (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a)
    (hC : OCF.Denis.C s a (OCF.Denis.psi s k a) (denote s t)) :
    RepresentedClosureStage s k a (denote s t) := by
  classical
  have small (u : Term) (hu : IsNormal s u) (hub : denote s u < OCF.Denis.I s 0 0)
      (huC : OCF.Denis.C s a (OCF.Denis.psi s k a) (denote s u)) :
      RepresentedClosureStage s k a (denote s u) := by
    exact representedClosureStage_of_lt s k a _ hk ha ⟨u, hu, rfl⟩
      (OCF.Denis.psi_closed s k a _ huC
        (OCF.Ordinal.lt_of_lt_of_le hub (OCF.Denis.regularIndex_lower_bound s k hk)))
  induction ht with
  | small ht hsmall => exact small _ ht hsmall hC
  | @index r b hr hb hn ihr ihb =>
    cases hn with
    | index hrn hbn hrl hbl =>
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ _ _ hrl hbl hC
      obtain ⟨c, hc, hca, hcr, hcb⟩ := representedClosureStage_pair s k a _ _ (ihr hrC) (ihb hbC)
      exact ⟨c, hc, hca, OCF.Denis.C_index s _ _ _ _ hcr hcb⟩
  | @sum p b hp hb hn ihp ihb =>
    obtain ⟨hpC, hbC⟩ := C_normal_sum_components s _ _ p b hn hC
    obtain ⟨c, hc, hca, hcp, hcb⟩ := representedClosureStage_pair s k a _ _ (ihp hpC) (ihb hbC)
    exact ⟨c, hc, hca, OCF.Denis.C_add s _ _ _ _ hcp hcb⟩
  | @collapse r b hr hb hbsmall ihr =>
    by_cases hlt : denote s (successorRankCollapseTerm r b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha
        ⟨_, successorRankCollapseTerm_normal s r b hr.normal hb hbsmall, rfl⟩ hlt
    · rw [denote_successorRankCollapseTerm] at hC hlt ⊢
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_successor_rank_small_parameters s _ _ a _
        (normal_rankBounded s r hr.normal) hbsmall hC
      have hba := OCF.Denis.C_collapse_argument_lt s a _ _ _ (Or.inl ⟨succ (denote s r), rfl⟩)
        ((not_lt_iff_le _ _).mp hlt) hC
      exact representedClosureStage_successorRankCollapse s k a _ _ ha ⟨b, hb, rfl⟩ hba
        (ihr hrC) (small b hb hbsmall hbC)
  | @collapseBelow r b hr hb hbindex hbarg ihr ihb =>
    by_cases hlt : denote s (successorRankCollapseTerm r b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha
        ⟨_, successorRankCollapseTerm_normal_of_mem s r b hr.normal hb.normal hbarg, rfl⟩ hlt
    · rw [denote_successorRankCollapseTerm] at hC hlt ⊢
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_successor_rank_below_parameters s _ _ a _
        (normal_rankBounded s r hr.normal) hbindex hbarg hC
      have hba := OCF.Denis.C_collapse_argument_lt s a _ _ _ (Or.inl ⟨succ (denote s r), rfl⟩)
        ((not_lt_iff_le _ _).mp hlt) hC
      exact representedClosureStage_successorRankCollapse s k a _ _ ha ⟨b, hb.normal, rfl⟩ hba
        (ihr hrC) (ihb hbC)
  | @firstCollapseBelow r b hr hb hbindex hbarg ihr ihb =>
    by_cases hlt : denote s (.psi (.I r .zero) b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha
        ⟨_, firstRankCollapse_normal_of_mem s r b hr.normal hb.normal hbarg, rfl⟩ hlt
    · change OCF.Denis.C s a _ (OCF.Denis.psi s (OCF.Denis.I s (denote s r) 0) (denote s b)) at hC
      change ¬ OCF.Denis.psi s (OCF.Denis.I s (denote s r) 0) (denote s b) < _ at hlt
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_first_rank_below_parameters s _ _ a _
        (normal_rankBounded s r hr.normal) hbindex hbarg hC
      have hba := OCF.Denis.C_collapse_argument_lt s a _ _ _ (Or.inl ⟨denote s r, rfl⟩)
        ((not_lt_iff_le _ _).mp hlt) hC
      obtain ⟨c, hc, hca, hcr⟩ := ihr hrC
      exact representedClosureStage_collapse s k a _ _ ha (Or.inl ⟨denote s r, rfl⟩)
        ⟨b, hb.normal, rfl⟩ hba
        ⟨c, hc, hca, OCF.Denis.C_index s c _ _ 0 hcr (OCF.Denis.C_zero s c _)⟩ (ihb hbC)
  | @properCollapseBelow r v b hr hv hb hn hbindex hindex ihr ihv ihb =>
    by_cases hlt : denote s (.psi (.I r v) b) < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha ⟨_, hn, rfl⟩ hlt
    · cases hn with
      | collapse hl hb hreg harg =>
        cases hl with
        | index hr hv hrl hvl =>
          obtain ⟨hlC, hbC⟩ := OCF.Denis.C_proper_collapse_parameters_below s _ _ _ a _ hreg hrl hvl
            hbindex hindex harg hC
          obtain ⟨hrC, hvC⟩ := OCF.Denis.C_normal_index_parameters s a _ _ _ hrl hvl hlC
          have hba := OCF.Denis.C_collapse_argument_lt s a _ _ _ hreg ((not_lt_iff_le _ _).mp hlt) hC
          obtain ⟨c, hc, hca, hcr, hcv⟩ := representedClosureStage_pair s k a _ _ (ihr hrC) (ihv hvC)
          exact representedClosureStage_collapse s k a _ _ ha hreg ⟨b, hb, rfl⟩ hba
            ⟨c, hc, hca, OCF.Denis.C_index s c _ _ _ hcr hcv⟩ (ihb hbC)
  | equalValue hu hn heq ih =>
    rw [heq] at hC ⊢
    exact ih hC

end
end T.Correspondence.Denis.Covering
