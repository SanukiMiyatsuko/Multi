import Multi.Constructive.Term2Inverse

namespace T.Constructive

open T

/-- Locate a normal term between consecutive entries without selecting a
least ordinal: the witness is found by induction on the source term. -/
theorem fund_omega_bracket (s l r : T) (hs : T.isNF s) (hd : T.dom s = .Ω l)
    (hr : T.isNF r) (hlow : T.fund s Z ≤ r) (hrs : r < s) :
    ∃ t, T.isNF t ∧ t < P l Z Z ∧ T.fund s t ≤ r ∧
      r < T.fund s (t + P Z Z Z) := by
  induction hs generalizing l r with
  | z => cases hd
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    cases r with
    | Z =>
      have heq : T.fund (P a b c) Z = Z := by
        cases hlow with
        | inl hlt => exact False.elim (lt_Z_inv _ hlt)
        | inr heq => exact heq
      refine ⟨Z, T.isNF.z, T.lt.Z_lt_P l Z Z, Or.inr heq, ?_⟩
      have hstrict := T.fund_omega_strict (P a b c) l hd Z (Z + P Z Z Z) (T.lt_add_one Z)
      rw [heq] at hstrict
      exact hstrict
    | P d e f =>
      have hrparts := T.isNF_components d e f hr
      by_cases hcZ : c = Z
      · cases hcZ
        rw [T.dom, ite_eq_left rfl] at hd
        cases hbdom : T.dom b with
        | Zero =>
          have hbZ := T.dom_eq_zero b hbdom
          cases hbZ
          rw [hbdom] at hd
          cases hadom : T.dom a with
          | Zero => rw [hadom] at hd; cases hd
          | One =>
            rw [hadom] at hd
            cases hd
            refine ⟨P d e f, hr, hrs, ?_, ?_⟩
            · rw [fund_index, hadom]
              exact Or.inr rfl
            · rw [fund_index, hadom]
              exact T.lt_add_one (P d e f)
          | ω => rw [hadom] at hd; cases hd
          | Ω m =>
            rw [hadom] at hd
            cases hd
            rw [fund_index, hadom] at hlow
            have hdlo := T.first_le_of_P_le _ Z Z d e f hlow
            have hdhi : d < a := by
              cases hrs with
              | p_first _ _ _ _ _ _ h => exact h
              | p_second _ _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
              | p_third _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
            cases ih0 l d hadom hrparts.1 hdlo hdhi with
            | intro t ht =>
              refine ⟨t, ht.1, ht.2.1, ?_, ?_⟩
              · rw [fund_index, hadom]
                exact T.index_le_P _ d e f ht.2.2.1
              · rw [fund_index, hadom]
                exact T.lt.p_first _ _ _ _ _ _ ht.2.2.2
        | One => rw [hbdom] at hd; cases hd
        | ω => rw [hbdom] at hd; cases hd
        | Ω m =>
          rw [hbdom] at hd
          change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
          by_cases ham : a < m
          · rw [ite_eq_left ham] at hd; cases hd
          · rw [ite_eq_right ham] at hd
            cases hd
            have hla := T.le_of_not_lt a l ham
            rw [fund_principal_uncollapsed a b l Z hbdom hla] at hlow
            have h0 := partial_order.antisymm d a
              (T.first_le_of_P_le d e f a b Z (Or.inl hrs))
              (T.first_le_of_P_le a _ Z d e f hlow)
            cases h0
            have helo := T.second_le_of_P_le a _ Z e f hlow
            have hehi : e < b := by
              cases hrs with
              | p_first _ _ _ _ _ _ h => exact False.elim (T.lt_irrefl a h)
              | p_second _ _ _ _ _ h => exact h
              | p_third _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
            cases ih1 l e hbdom hrparts.2.1 helo hehi with
            | intro t ht =>
              refine ⟨t, ht.1, ht.2.1, ?_, ?_⟩
              · rw [fund_principal_uncollapsed a b l t hbdom hla]
                exact principal_le_of_argument_le a _ e f ht.2.2.1
              · rw [fund_principal_uncollapsed a b l (t + P Z Z Z) hbdom hla]
                exact T.lt.p_second _ _ _ _ _ ht.2.2.2
      · rw [T.dom, ite_eq_right hcZ] at hd
        rw [fund_nonzero_tail_eq a b c Z hcZ] at hlow
        have h0 := partial_order.antisymm d a
          (T.first_le_of_P_le d e f a b c (Or.inl hrs))
          (T.first_le_of_P_le a b _ d e f hlow)
        cases h0
        have h1 := partial_order.antisymm e b
          (T.second_le_of_P_le a e f b c (Or.inl hrs))
          (T.second_le_of_P_le a b _ e f hlow)
        cases h1
        have hflo := T.third_le_of_P_le a b _ f hlow
        have hfhi : f < c := by
          cases hrs with
          | p_first _ _ _ _ _ _ h => exact False.elim (T.lt_irrefl a h)
          | p_second _ _ _ _ _ h => exact False.elim (T.lt_irrefl b h)
          | p_third _ _ _ _ h => exact h
        cases ih2 l f hd hrparts.2.2 hflo hfhi with
        | intro t ht =>
          refine ⟨t, ht.1, ht.2.1, ?_, ?_⟩
          · rw [fund_nonzero_tail_eq a b c t hcZ]
            cases ht.2.2.1 with
            | inl hlt => exact Or.inl (T.lt.p_third _ _ _ _ hlt)
            | inr heq => rw [heq]; exact Or.inr rfl
          · rw [fund_nonzero_tail_eq a b c (t + P Z Z Z) hcZ]
            exact T.lt.p_third _ _ _ _ ht.2.2.2

theorem relative_cofinal_omega (X : T.NF → Prop) (s r : T.NF) (l : T)
    (hd : T.dom s.1 = .Ω l) (hr : Stage X r) (hrs : r.1 < s.1) :
    ∃ c : T.NF, Step (Stage X) c s ∧ r.1 ≤ c.1 := by
  by_cases hlo : T.fund s.1 Z ≤ r.1
  · cases fund_omega_bracket s.1 l r.1 s.2 hd r.2 hlo hrs with
    | intro t ht =>
      have htStage := stage_of_omega_interval X s.1 l t s.2 hd ht.1 ht.2.1 r hr
        ht.2.2.1 ht.2.2.2
      have hlne : l ≠ Z := by
        intro hl
        have hlOne := T.dom_omega_index_one s.1 l hd
        rw [hl] at hlOne
        cases hlOne
      have htSuccNF := T.add_one_isNF t ht.1
      have htSuccBound := T.add_one_lt_index t l hlne ht.2.1
      let u : T.NF := ⟨t + P Z Z Z, htSuccNF⟩
      have huInput : Input (Stage X) s u := by
        unfold Input
        rw [hd]
        exact ⟨htSuccBound, Or.inl (stage_add_one htStage)⟩
      exact ⟨⟨T.fund s.1 u.1, fund_isNF_of_input huInput⟩,
        ⟨u, huInput, rfl⟩, Or.inl ht.2.2.2⟩
  · have hrlo : r.1 < T.fund s.1 Z := by
      cases T.lt_total r.1 (T.fund s.1 Z) with
      | inl h => exact h
      | inr h =>
        cases h with
        | inl h => exact False.elim (hlo (Or.inl h))
        | inr h => exact False.elim (hlo (Or.inr h.symm))
    have hzInput : Input (Stage X) s ⟨Z, T.isNF.z⟩ := by
      unfold Input
      rw [hd]
      exact ⟨T.lt.Z_lt_P l Z Z, Or.inl (stage_zero X)⟩
    exact ⟨⟨T.fund s.1 Z, fund_isNF_of_input hzInput⟩,
      ⟨⟨Z, T.isNF.z⟩, hzInput, rfl⟩, Or.inl hrlo⟩

theorem reduction_cofinal : reduction.Cofinal := by
  intro X s r hs hr hrs
  change r.1 < s.1 at hrs
  have hraw : ∃ c : T.NF, Step (Stage X) c s ∧ r.1 ≤ c.1 := by
    cases hd : T.dom s.1 with
    | Zero =>
      have hz := T.dom_eq_zero s.1 hd
      rw [hz] at hrs
      exact False.elim (lt_Z_inv _ hrs)
    | One =>
      exact relative_cofinal_nonomega X s r (fun l h => by rw [hd] at h; cases h) hrs
    | ω =>
      exact relative_cofinal_nonomega X s r (fun l h => by rw [hd] at h; cases h) hrs
    | Ω l => exact relative_cofinal_omega X s r l hd hr hrs
  cases hraw with
  | intro c hc =>
    refine ⟨c, hc.1, ?_⟩
    cases hc.2 with
    | inl hlt => exact Or.inl hlt
    | inr heq => exact Or.inr (Subtype.ext heq)

theorem universal_wellFounded :
    WellFounded (fun a b : {s : T.NF // reduction.Universal s} => a.1.1 < b.1.1) :=
  reduction.universal_wellFounded reduction_cofinal

end T.Constructive
