import Multi.term2.Constructive.Term2Anchors

namespace T.Constructive

open T

theorem dom_index_of_limit (a : T) (h0 : T.dom a ≠ .Zero) (h1 : T.dom a ≠ .One) :
    T.dom (P a Z Z) = T.dom a := by
  rw [dom_index]
  cases hd : T.dom a with
  | Zero => exact False.elim (h0 hd)
  | One => exact False.elim (h1 hd)
  | ω => rfl
  | Ω l => rfl

theorem fund_index_of_limit (a t : T) (h0 : T.dom a ≠ .Zero) (h1 : T.dom a ≠ .One) :
    T.fund (P a Z Z) t = P (T.fund a t) Z Z := by
  rw [fund_index]
  cases hd : T.dom a with
  | Zero => exact False.elim (h0 hd)
  | One => exact False.elim (h1 hd)
  | ω => rfl
  | Ω l => rfl

theorem fund_principal_uncollapsed (a b l t : T) (hd : T.dom b = .Ω l) (hle : l ≤ a) :
    T.fund (P a b Z) t = P a (T.fund b t) Z := by
  have hnot : ¬ a < l := by
    intro hal
    exact T.lt_irrefl a (lt_of_lt_of_le_thm T a l a hal hle)
  rw [T.fund, ite_eq_left rfl, hd]
  exact ite_eq_right hnot

theorem dom_principal_uncollapsed (a b l : T) (hd : T.dom b = .Ω l) (hle : l ≤ a) :
    T.dom (P a b Z) = .Ω l := by
  have hnot : ¬ a < l := by
    intro hal
    exact T.lt_irrefl a (lt_of_lt_of_le_thm T a l a hal hle)
  rw [T.dom, ite_eq_left rfl, hd]
  exact ite_eq_right hnot

theorem fund_principal_countable (a b t : T) (hd : T.dom b = .ω) :
    T.fund (P a b Z) t = P a (T.fund b t) Z := by
  rw [T.fund, ite_eq_left rfl, hd]

theorem fund_nonzero_tail_eq (a b c t : T) (hc : c ≠ Z) :
    T.fund (P a b c) t = P a b (T.fund c t) := by
  rw [T.fund, ite_eq_right hc]

theorem dom_index_lt_of_below (t l m : T) (ht : T.isNF t) (hd : T.dom t = .Ω m)
    (hbound : t < P l Z Z) : m < l := by
  cases T.dom_omega_index_bound t ht m hd with
  | intro a ha =>
    cases ha with
    | intro b hb =>
      cases hb with
      | intro c hc =>
        rw [hc.1] at hbound
        have hal : a < l := by
          cases hbound with
          | p_first _ _ _ _ _ _ h => exact h
          | p_second _ _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
          | p_third _ _ _ _ h => exact False.elim (lt_Z_inv _ h)
        exact lt_of_le_of_lt_thm T m a l hc.2 hal

theorem fund_omega_commutation (s l t : T) (hs : T.isNF s) (hd : T.dom s = .Ω l)
    (ht : T.isNF t) (hbound : t < P l Z Z)
    (h0 : T.dom t ≠ .Zero) (h1 : T.dom t ≠ .One) :
    T.dom (T.fund s t) = T.dom t ∧
      ∀ x, T.fund (T.fund s t) x = T.fund s (T.fund t x) := by
  induction hs generalizing l with
  | z => cases hd
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
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
          have hfund : ∀ x, T.fund (P a Z Z) x = x := by
            intro x
            rw [fund_index, hadom]
          rw [hfund t]
          exact ⟨rfl, fun x => (hfund (T.fund t x)).symm⟩
        | ω => rw [hadom] at hd; cases hd
        | Ω m =>
          rw [hadom] at hd
          cases hd
          have hp := ih0 l hadom hbound
          have hf0 : T.dom (T.fund a t) ≠ .Zero := fun h => h0 (hp.1.symm.trans h)
          have hf1 : T.dom (T.fund a t) ≠ .One := fun h => h1 (hp.1.symm.trans h)
          rw [fund_index, hadom]
          refine ⟨(dom_index_of_limit _ hf0 hf1).trans hp.1, ?_⟩
          intro x
          rw [fund_index_of_limit _ x hf0 hf1, hp.2 x, fund_index, hadom]
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
          have hp := ih1 l hbdom hbound
          rw [fund_principal_uncollapsed a b l t hbdom hla]
          cases htD : T.dom t with
          | Zero => exact False.elim (h0 htD)
          | One => exact False.elim (h1 htD)
          | ω =>
            have hft : T.dom (T.fund b t) = .ω := hp.1.trans htD
            refine ⟨?_, ?_⟩
            · rw [T.dom, ite_eq_left rfl, hft]
            · intro x
              rw [fund_principal_countable a _ x hft, hp.2 x,
                fund_principal_uncollapsed a b l (T.fund t x) hbdom hla]
          | Ω m =>
            have hft : T.dom (T.fund b t) = .Ω m := hp.1.trans htD
            have hml := dom_index_lt_of_below t l m ht htD hbound
            have hma : m ≤ a := Or.inl (lt_of_lt_of_le_thm T m l a hml hla)
            refine ⟨dom_principal_uncollapsed a _ m hft hma, ?_⟩
            intro x
            rw [fund_principal_uncollapsed a _ m x hft hma, hp.2 x,
              fund_principal_uncollapsed a b l (T.fund t x) hbdom hla]
    · rw [T.dom, ite_eq_right hcZ] at hd
      have hp := ih2 l hd hbound
      have hct : T.fund c t ≠ Z := by
        intro heq
        have htZero : T.dom t = .Zero := by
          rw [heq] at hp
          exact hp.1.symm
        exact h0 htZero
      rw [fund_nonzero_tail_eq a b c t hcZ]
      refine ⟨?_, ?_⟩
      · rw [T.dom, ite_eq_right hct]
        exact hp.1
      · intro x
        rw [fund_nonzero_tail_eq a b _ x hct, hp.2 x,
          fund_nonzero_tail_eq a b c (T.fund t x) hcZ]

end T.Constructive
