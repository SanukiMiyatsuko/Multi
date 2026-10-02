import Multi.term3.Denis.CeilingInduction

/-! Closure support at represented earlier stages for every normal term.

With the general parameter recovery `C_proper_collapse_parameters`, the
restriction of `CollapseTree.representedClosureStage` to collapse trees is
removed: every normal term whose value lies in the closure of a limit
collapse is already generated at a represented earlier stage. Collapse
subterms are first replaced by proper presentations of the same value and
no larger size. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
open CollapseNormalization
noncomputable section

theorem normal_representedClosureStage (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (ha : OCF.Denis.IsLimit a) :
    ∀ t, IsNormal s t → OCF.Denis.C s a (OCF.Denis.psi s k a) (denote s t) →
      RepresentedClosureStage s k a (denote s t) := by
  intro t
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    intro ht hC
    by_cases hlt : denote s t < OCF.Denis.psi s k a
    · exact representedClosureStage_of_lt s k a _ hk ha ⟨t, ht, rfl⟩ hlt
    have hge : OCF.Denis.psi s k a ≤ denote s t := (not_lt_iff_le _ _).mp hlt
    cases ht with
    | zero => exact False.elim (hlt (OCF.Denis.psi_pos s k a
        (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s k hk))))
    | @sum p b hp hb hpp hpv hbpos hhead =>
      obtain ⟨hpC, hbC⟩ := C_normal_sum_components s _ _ p b
        (.sum hp hb hpp hpv hbpos hhead) hC
      have hpS := ih p (by change sizeOf p < sizeOf (Term.add p b); simp; omega) hp hpC
      have hbS := ih b (by change sizeOf b < sizeOf (Term.add p b); simp; omega) hb hbC
      obtain ⟨c, hc, hca, hcp, hcb⟩ := representedClosureStage_pair s k a _ _ hpS hbS
      exact ⟨c, hc, hca, OCF.Denis.C_add s c _ _ _ hcp hcb⟩
    | @index r b hr hb hrl hbl =>
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ _ _ hrl hbl hC
      have hrS := ih r (by change sizeOf r < sizeOf (Term.I r b); simp; omega) hr hrC
      have hbS := ih b (by change sizeOf b < sizeOf (Term.I r b); simp; omega) hb hbC
      obtain ⟨c, hc, hca, hcr, hcb⟩ := representedClosureStage_pair s k a _ _ hrS hbS
      exact ⟨c, hc, hca, OCF.Denis.C_index s c _ _ _ hcr hcb⟩
    | @collapse l b hl hb hreg harg =>
      have hn : IsNormal s (.psi l b) := .collapse hl hb hreg harg
      obtain ⟨u, hu, hueq, husize⟩ := exists_proper s (.psi l b) hn ⟨l, b, rfl⟩
      obtain ⟨r', b', a', rfl, hun, hidx⟩ := hu
      cases hun with
      | collapse hI ha' hreg' harg' =>
        have hval : denote s (.psi (.I r' b') a') = denote s (.psi l b) := hueq
        have hproper : OCF.Denis.ProperCollapse s (denote s (.I r' b')) (denote s a') :=
          ⟨hreg', hidx, harg'⟩
        have hC' : OCF.Denis.C s a (OCF.Denis.psi s k a)
            (OCF.Denis.psi s (denote s (.I r' b')) (denote s a')) := by
          change OCF.Denis.C s a _ (denote s (.psi (.I r' b') a'))
          rw [hval]
          exact hC
        have hge' : OCF.Denis.psi s k a ≤ OCF.Denis.psi s (denote s (.I r' b')) (denote s a') := by
          change OCF.Denis.psi s k a ≤ denote s (.psi (.I r' b') a')
          rw [hval]
          exact hge
        obtain ⟨ha'a, hIC, ha'C⟩ := OCF.Denis.C_proper_collapse_parameters s _ _ a _
          hproper hge' hC'
        have hsizeI : sizeOf (Term.I r' b') < sizeOf (Term.psi l b) := by
          have : sizeOf (Term.I r' b') < sizeOf (Term.psi (.I r' b') a') := by simp; omega
          omega
        have hsizea : sizeOf a' < sizeOf (Term.psi l b) := by
          have : sizeOf a' < sizeOf (Term.psi (.I r' b') a') := by simp; omega
          omega
        have hIS := ih (.I r' b') hsizeI hI hIC
        have haS := ih a' hsizea ha' ha'C
        have hres := representedClosureStage_collapse s k a _ _ ha hreg' ⟨a', ha', rfl⟩ ha'a hIS haS
        change RepresentedClosureStage s k a (denote s (.psi l b))
        rw [← hval]
        exact hres

end
end T.Correspondence.Denis.Covering
