import Multi.term2.Term2Syntax
import Multi.term2.OCF.Hierarchy

/- Optional classical interpretation, independent of the constructive proof in Multi.term2. -/
namespace T

open OCF

noncomputable def denote : T → Ordinal.{0}
  | Z => 0
  | P s0 s1 s2 => Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + denote s2

theorem denote_P (s0 s1 s2 : T) :
    denote (P s0 s1 s2) = Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + denote s2 := rfl

theorem denote_head_P (s0 s1 s2 : T) :
    denote (head (P s0 s1 s2)) = Collapse.psi Collapse.hierarchy (denote s0) (denote s1) := by
  change Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + 0 = _
  exact Ordinal.add_zero _

theorem denote_P_pos (s0 s1 s2 : T) : 0 < denote (P s0 s1 s2) :=
  Ordinal.lt_of_lt_of_le (Ordinal.lt_of_lt_of_le (Collapse.hierarchy_pos (denote s0))
    (Collapse.psi_lower_bound Collapse.hierarchy (denote s0) (denote s1)))
    (Ordinal.le_add _ (denote s2))

/-- Order preservation, closure membership, and a principal upper bound are proved together. -/
theorem interpretation_properties (s : T) (hs : isNF s) :
    (∀ t, s < t → denote s < denote t) ∧
    (∀ u b, (∀ x, x ∈ G u s → denote x < b) →
      Collapse.C Collapse.hierarchy (denote u) b (denote s)) ∧
    (∀ b, Ordinal.AddPrincipal b → denote (head s) < b → denote s < b) := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
    cases s with
    | Z =>
      apply And.intro
      · intro t ht
        cases t with
        | Z => exact False.elim (lt_Z_Z_inv ht)
        | P t0 t1 t2 => exact denote_P_pos t0 t1 t2
      · apply And.intro
        · intro u b hb
          exact Collapse.C_base Collapse.hierarchy (denote u) b 0 (Collapse.hierarchy_pos (denote u))
        · intro b hb hZ
          exact hZ
    | P s0 s1 s2 =>
      cases hs with
      | p _ _ _ hs0 hs1 hs2 hG hhead =>
        have ih0 := ih s0 (size_lt_size_P_first s0 s1 s2) hs0
        have ih1 := ih s1 (size_lt_size_P_second s0 s1 s2) hs1
        have ih2 := ih s2 (size_lt_size_P_third s0 s1 s2) hs2
        have headBound : denote (head s2) ≤ denote (head (P s0 s1 s2)) := by
          cases hhead with
          | inl hlt =>
            have hsmall := Nat.lt_of_le_of_lt (head_size_le s2) (size_lt_size_P_third s0 s1 s2)
            exact Or.inl ((ih (head s2) hsmall (head_isNF s2 hs2)).1 (P s0 s1 Z) hlt)
          | inr heq => exact Or.inr (congrArg denote heq)
        have bounded : ∀ b, Ordinal.AddPrincipal b →
            denote (head (P s0 s1 s2)) < b → denote (P s0 s1 s2) < b := by
          intro b hb hfirst
          have htail := ih2.2.2 b hb (Ordinal.lt_of_le_of_lt headBound hfirst)
          rw [denote_head_P] at hfirst
          exact hb _ _ hfirst htail
        have regular : Collapse.C Collapse.hierarchy (denote s0) (denote s1) (denote s1) := by
          apply ih1.2.1 s0 (denote s1)
          intro x hx
          have hp := mem_G_properties s0 s1 x hs1 hx
          have hsmall := Nat.lt_trans hp.2 (size_lt_size_P_second s0 s1 s2)
          exact (ih x hsmall hp.1).1 s1 (hG x hx)
        apply And.intro
        · intro t hst
          cases t with
          | Z => exact False.elim (lt_P_Z_inv s0 s1 s2 hst)
          | P t0 t1 t2 =>
            cases lt_inv s0 s1 s2 t0 t1 t2 hst with
            | inl h0 =>
              have hpsi := Collapse.psi_lt_hierarchy (denote s0) (denote t0) (denote s1) (ih0.1 t0 h0)
              have hsource : denote (P s0 s1 s2) < Collapse.hierarchy (denote t0) := by
                apply bounded _ (Collapse.hierarchy_principal (denote t0))
                rw [denote_head_P]
                exact hpsi
              exact Ordinal.lt_of_lt_of_le hsource
                (Ordinal.le_trans (Collapse.psi_lower_bound Collapse.hierarchy (denote t0) (denote t1))
                  (Ordinal.le_add _ (denote t2)))
            | inr hrest =>
              cases hrest with
              | inl h1 =>
                have heq := h1.1
                have hlt := h1.2
                cases heq
                have hpsi := Collapse.psi_argument_strict (denote s0) (denote s1) (denote t1)
                  (ih1.1 t1 hlt) regular
                have hsource : denote (P s0 s1 s2) <
                    Collapse.psi Collapse.hierarchy (denote s0) (denote t1) := by
                  apply bounded _ (Collapse.psi_hierarchy_principal (denote s0) (denote t1))
                  rw [denote_head_P]
                  exact hpsi
                exact Ordinal.lt_of_lt_of_le hsource (Ordinal.le_add _ (denote t2))
              | inr h2 =>
                have e0 := h2.1
                have e1 := h2.2.1
                have hlt := h2.2.2
                cases e0
                cases e1
                exact Ordinal.add_lt_add_right _ (ih2.1 t2 hlt)
        · apply And.intro
          · intro u b hb
            cases (inferInstance : Decidable (u ≤ s0)) with
            | isTrue hu =>
              have hmember : s1 ∈ G u (P s0 s1 s2) := by
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_left _
                  (List.mem_append_left _ (List.mem_singleton_self s1)))
              have hc0 : Collapse.C Collapse.hierarchy (denote u) b (denote s0) := by
                apply ih0.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
              have hc1 : Collapse.C Collapse.hierarchy (denote u) b (denote s1) := by
                apply ih1.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_right _ hx)
              have hc2 : Collapse.C Collapse.hierarchy (denote u) b (denote s2) := by
                apply ih2.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_right _ hx
              exact Collapse.C_step Collapse.hierarchy (denote u) b
                (denote s0) (denote s1) (denote s2) (hb s1 hmember) hc0 hc1 hc2 regular
            | isFalse hu =>
              have hindex : s0 < u := by
                cases T.lt_total s0 u with
                | inl h => exact h
                | inr hrest =>
                  cases hrest with
                  | inl h => exact False.elim (hu (Or.inl h))
                  | inr h => exact False.elim (hu (Or.inr h.symm))
              apply Collapse.C_base Collapse.hierarchy (denote u) b (denote (P s0 s1 s2))
              apply bounded _ (Collapse.hierarchy_principal (denote u))
              rw [denote_head_P]
              exact Collapse.psi_lt_hierarchy (denote s0) (denote u) (denote s1) (ih0.1 u hindex)
          · exact bounded

theorem denote_strict (s t : T) (hs : isNF s) (hst : s < t) : denote s < denote t :=
  (interpretation_properties s hs).1 t hst

end T
