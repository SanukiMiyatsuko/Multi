import Multi.term2.Constructive.Term2Stages

namespace T.Constructive

open T

/-- A fixed, admissible branch used when comparing neighboring sequence values. -/
def anchor (s : T) : T :=
  match T.dom s with
  | .Ω l => P (T.fund l Z) Z Z
  | .ω => T.ofNat 1
  | _ => Z

theorem anchor_isNF (s : T) (hs : T.isNF s) : T.isNF (anchor s) := by
  unfold anchor
  cases hd : T.dom s with
  | Zero => exact T.isNF.z
  | One => exact T.isNF.z
  | ω => exact T.ofNat_isNF 1
  | Ω l =>
    exact T.isNF_index _ (T.fund_one_isNF l (T.dom_omega_index_isNF s l hs hd)
      (T.dom_omega_index_one s l hd) Z)

theorem anchor_input (X : T.NF → Prop) (s : T.NF) (hne : s.1 ≠ Z) :
    Input X s ⟨anchor s.1, anchor_isNF s.1 s.2⟩ := by
  cases hd : T.dom s.1 with
  | Zero => exact False.elim (hne (T.dom_eq_zero s.1 hd))
  | One =>
    unfold Input
    rw [hd]
    change anchor s.1 = Z
    unfold anchor
    rw [hd]
  | ω =>
    unfold Input
    rw [hd]
    refine ⟨1, ?_⟩
    change anchor s.1 = T.ofNat 1
    unfold anchor
    rw [hd]
  | Ω l =>
    unfold Input
    rw [hd]
    have heq : anchor s.1 = P (T.fund l Z) Z Z := by unfold anchor; rw [hd]
    have hl := T.dom_omega_index_one s.1 l hd
    have hlne : l ≠ Z := by
      intro heq
      rw [heq] at hl
      cases hl
    have hpred : T.fund l Z < l := T.fund_lt_of_domain l Z hlne (by
      intro m hm
      rw [hl] at hm
      cases hm)
    refine ⟨?_, Or.inr heq⟩
    change anchor s.1 < P l Z Z
    rw [heq]
    exact T.lt.p_first _ _ _ _ _ _ hpred

theorem fund_anchor_lt (s : T) (hs : T.isNF s) (hne : s ≠ Z) : T.fund s (anchor s) < s :=
  fund_lt_of_input (anchor_input (fun _ => False) ⟨s, hs⟩ hne)

theorem stage_anchor {X : T.NF → Prop} {s : T.NF} (hs : Stage X s) (hne : s.1 ≠ Z) :
    Stage X ⟨T.fund s.1 (anchor s.1), fund_isNF_of_input (anchor_input X s hne)⟩ :=
  stage_fund hs (anchor_input X s hne)

theorem fund_omega_mono (s l x y : T) (hd : T.dom s = .Ω l) (hxy : x ≤ y) :
    T.fund s x ≤ T.fund s y := by
  cases hxy with
  | inl hlt => exact Or.inl (T.fund_omega_strict s l hd x y hlt)
  | inr heq => cases heq; exact Or.inr rfl

theorem fund_anchor_principal_lower (a b : T) (hb : b ≠ Z) :
    P a (T.fund b (anchor b)) Z ≤ T.fund (P a b Z) (anchor (P a b Z)) := by
  cases hd : T.dom b with
  | Zero => exact False.elim (hb (T.dom_eq_zero b hd))
  | One =>
    have hs : T.dom (P a b Z) = .ω := by rw [T.dom, ite_eq_left rfl, hd]
    unfold anchor
    rw [hs, hd, T.fund, ite_eq_left rfl, hd]
    exact Or.inr rfl
  | ω =>
    have hs : T.dom (P a b Z) = .ω := by rw [T.dom, ite_eq_left rfl, hd]
    unfold anchor
    rw [hs, hd, T.fund, ite_eq_left rfl, hd]
    exact Or.inr rfl
  | Ω l =>
    by_cases hal : a < l
    · have hs : T.dom (P a b Z) = .ω := by
        rw [T.dom, ite_eq_left rfl, hd]
        exact ite_eq_left hal
      unfold anchor
      rw [hs, hd, T.fund, ite_eq_left rfl, hd]
      change P a (T.fund b (P (T.fund l Z) Z Z)) Z ≤
        (if a < l then P a (T.fund b (P (T.fund l Z) (T.fund b Z) Z)) Z else _)
      rw [ite_eq_left hal]
      have hi : P (T.fund l Z) Z Z ≤ P (T.fund l Z) (T.fund b Z) Z :=
        T.index_le_P _ _ _ _ (Or.inr rfl)
      cases fund_omega_mono b l _ _ hd hi with
      | inl hlt => exact Or.inl (T.lt.p_second _ _ _ _ _ hlt)
      | inr heq => rw [heq]; exact Or.inr rfl
    · have hs : T.dom (P a b Z) = .Ω l := by
        rw [T.dom, ite_eq_left rfl, hd]
        exact ite_eq_right hal
      unfold anchor
      rw [hs, hd, T.fund, ite_eq_left rfl, hd]
      change P a (T.fund b (P (T.fund l Z) Z Z)) Z ≤ (if a < l then _ else _)
      rw [ite_eq_right hal]
      exact Or.inr rfl

theorem fund_anchor_index (a : T) (ha : a ≠ Z) :
    T.fund (P a Z Z) (anchor (P a Z Z)) = P (T.fund a (anchor a)) Z Z := by
  cases hd : T.dom a with
  | Zero => exact False.elim (ha (T.dom_eq_zero a hd))
  | One =>
    unfold anchor
    rw [dom_index, hd, fund_index, hd]
  | ω =>
    unfold anchor
    rw [dom_index, hd, fund_index, hd]
  | Ω l =>
    unfold anchor
    rw [dom_index, hd, fund_index, hd]

theorem index_le_fund_anchor (a b c : T) (h : b ≠ Z ∨ c ≠ Z) :
    P a Z Z ≤ T.fund (P a b c) (anchor (P a b c)) := by
  by_cases hc : c = Z
  · cases hc
    have hb : b ≠ Z := by
      cases h with
      | inl hb => exact hb
      | inr hc => exact False.elim (hc rfl)
    exact partial_order.trans _ _ _
      (T.index_le_P a a (T.fund b (anchor b)) Z (Or.inr rfl))
      (fund_anchor_principal_lower a b hb)
  · rw [T.fund, ite_eq_right hc]
    exact T.index_le_P _ _ _ _ (Or.inr rfl)

theorem anchor_nonzero_tail (a b c : T) (hc : c ≠ Z) : anchor (P a b c) = anchor c := by
  unfold anchor
  rw [T.dom, ite_eq_right hc]

theorem principal_le_of_argument_le (a b d c : T) (h : b ≤ d) : P a b Z ≤ P a d c := by
  cases h with
  | inl hlt => exact Or.inl (T.lt.p_second _ _ _ _ _ hlt)
  | inr heq => cases heq; exact T.head_le (P a b c)

theorem fund_omega_bachmann (s l t r : T) (hd : T.dom s = .Ω l) (hr : T.isNF r)
    (hlo : T.fund s t < r) (hhi : r ≤ T.fund s (t + P Z Z Z)) :
    T.fund s t ≤ T.fund r (anchor r) := by
  induction s generalizing l r with
  | Z => cases hd
  | P a b c ih0 ih1 ih2 =>
    cases r with
    | Z => exact False.elim (lt_Z_inv _ hlo)
    | P d e f =>
      have hrparts := T.isNF_components d e f hr
      by_cases hc : c = Z
      · cases hc
        rw [T.dom, ite_eq_left rfl] at hd
        cases hb : T.dom b with
        | Zero =>
          have hbZ := T.dom_eq_zero b hb
          cases hbZ
          rw [hb] at hd
          rw [fund_index] at hlo hhi ⊢
          cases ha : T.dom a with
          | Zero => rw [ha] at hd; cases hd
          | One =>
            rw [ha] at hlo hhi
            change t < P d e f at hlo
            change P d e f ≤ t + P Z Z Z at hhi
            change t ≤ T.fund (P d e f) (anchor (P d e f))
            have heq : P d e f = t + P Z Z Z := by
              cases hhi with
              | inr heq => exact heq
              | inl hlt =>
                have hle := (T.fund_one_properties (t + P Z Z Z) (T.dom_add_one t)).2.2.1
                  (P d e f) hlt
                rw [T.fund_add_one] at hle
                exact False.elim (T.lt_irrefl t
                  (lt_of_lt_of_le_thm T t (P d e f) t hlo hle))
            rw [heq, T.fund_add_one]
            exact Or.inr rfl
          | ω => rw [ha] at hd; cases hd
          | Ω m =>
            rw [ha] at hd
            cases hd
            rw [ha] at hlo hhi
            change P (T.fund a t) Z Z < P d e f at hlo
            change P d e f ≤ P (T.fund a (t + P Z Z Z)) Z Z at hhi
            change P (T.fund a t) Z Z ≤ T.fund (P d e f) (anchor (P d e f))
            have hfirst := T.first_le_of_P_le d e f (T.fund a (t + P Z Z Z)) Z Z hhi
            by_cases he : e = Z
            · cases he
              by_cases hf : f = Z
              · cases hf
                have hlow : T.fund a t < d := by
                  cases hlo with
                  | p_first _ _ _ _ _ _ h => exact h
                  | p_second _ _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
                  | p_third _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
                have hdne : d ≠ Z := by intro h; rw [h] at hlow; exact lt_Z_inv _ hlow
                rw [fund_anchor_index d hdne]
                cases ih0 l d ha hrparts.1 hlow hfirst with
                | inl hlt => exact Or.inl (T.lt.p_first _ _ _ _ _ _ hlt)
                | inr heq => rw [heq]; exact Or.inr rfl
              · have hlow := T.first_le_of_P_le _ Z Z d Z f (Or.inl hlo)
                exact partial_order.trans _ _ _
                  (T.index_le_P _ _ Z Z hlow) (index_le_fund_anchor d Z f (Or.inr hf))
            · have hlow := T.first_le_of_P_le _ Z Z d e f (Or.inl hlo)
              exact partial_order.trans _ _ _
                (T.index_le_P _ _ Z Z hlow) (index_le_fund_anchor d e f (Or.inl he))
        | One => rw [hb] at hd; cases hd
        | ω => rw [hb] at hd; cases hd
        | Ω m =>
          rw [hb] at hd
          change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
          by_cases ham : a < m
          · rw [ite_eq_left ham] at hd; cases hd
          · rw [ite_eq_right ham] at hd
            cases hd
            rw [T.fund, ite_eq_left rfl, hb] at hlo hhi ⊢
            change (if a < l then _ else _) < P d e f at hlo
            change P d e f ≤ (if a < l then _ else _) at hhi
            change (if a < l then _ else _) ≤ _
            rw [ite_eq_right ham] at hlo hhi ⊢
            have heq := partial_order.antisymm d a
              (T.first_le_of_P_le d e f a _ Z hhi)
              (T.first_le_of_P_le a _ Z d e f (Or.inl hlo))
            cases heq
            have hupper := T.second_le_of_P_le a e f _ Z hhi
            by_cases hf : f = Z
            · cases hf
              have hlower : T.fund b t < e := by
                cases hlo with
                | p_first _ _ _ _ _ _ h => exact False.elim (T.lt_irrefl a h)
                | p_second _ _ _ _ _ h => exact h
                | p_third _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
              have hene : e ≠ Z := by intro h; rw [h] at hlower; exact lt_Z_inv _ hlower
              exact partial_order.trans _ _ _
                (principal_le_of_argument_le a _ _ Z (ih1 l e hb hrparts.2.1 hlower hupper))
                (fund_anchor_principal_lower a e hene)
            · have hlower := T.second_le_of_P_le a _ Z e f (Or.inl hlo)
              rw [T.fund, ite_eq_right hf]
              exact principal_le_of_argument_le a _ e _ hlower
      · rw [T.dom, ite_eq_right hc] at hd
        rw [T.fund, ite_eq_right hc] at hlo hhi ⊢
        have h0 := partial_order.antisymm d a
          (T.first_le_of_P_le d e f a b _ hhi)
          (T.first_le_of_P_le a b _ d e f (Or.inl hlo))
        cases h0
        have h1 := partial_order.antisymm e b
          (T.second_le_of_P_le a e f b _ hhi)
          (T.second_le_of_P_le a b _ e f (Or.inl hlo))
        cases h1
        have hupper := T.third_le_of_P_le a b f _ hhi
        have hlower : T.fund c t < f := by
          cases hlo with
          | p_first _ _ _ _ _ _ h => exact False.elim (T.lt_irrefl a h)
          | p_second _ _ _ _ _ h => exact False.elim (T.lt_irrefl b h)
          | p_third _ _ _ _ h => exact h
        have hf : f ≠ Z := by intro h; rw [h] at hlower; exact lt_Z_inv _ hlower
        rw [T.fund, ite_eq_right hf, anchor_nonzero_tail a b f hf]
        cases ih2 l f hd hrparts.2.2 hlower hupper with
        | inl hlt => exact Or.inl (T.lt.p_third _ _ _ _ hlt)
        | inr heq => rw [heq]; exact Or.inr rfl

end T.Constructive
