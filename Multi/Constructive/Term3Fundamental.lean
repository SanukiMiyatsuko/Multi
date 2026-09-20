import Multi.Term3Syntax

open T

theorem T.fund_Z (t : T) : T.fund Z t = Z := by rw [T.fund]

theorem T.dom_eq_zero (s : T) (h : T.dom s = .Zero) : s = Z := by
  induction s with
  | Z => rfl
  | P a b c d ih0 ih1 ih2 ih3 =>
    rw [T.dom] at h
    split at h
    · cases hc : T.dom c with
      | Zero =>
        rw [hc] at h
        cases hb : T.dom b with
        | Zero =>
          rw [hb] at h
          cases ha : T.dom a with
          | Zero => rw [ha] at h; cases h
          | One => rw [ha] at h; cases h
          | ω => rw [ha] at h; cases h
          | Ω l0 l1 => rw [ha] at h; cases h
        | One => rw [hb] at h; cases h
        | ω => rw [hb] at h; cases h
        | Ω l0 l1 =>
          rw [hb] at h
          change (if P a b Z Z < P l0 l1 Z Z then Dom.ω else Dom.Ω l0 l1) = Dom.Zero at h
          split at h
          · cases h
          · cases h
      | One => rw [hc] at h; cases h
      | ω => rw [hc] at h; cases h
      | Ω l0 l1 =>
        rw [hc] at h
        change (if P a b c Z < P l0 l1 Z Z then Dom.ω else Dom.Ω l0 l1) = Dom.Zero at h
        split at h
        · cases h
        · cases h
    · rename_i hd
      exact False.elim (hd (ih3 h))

/-- A large domain has a successor in its second coordinate, or a zero second
coordinate and a successor first coordinate. -/
theorem T.dom_omega_index_cases (s l0 l1 : T) (h : T.dom s = .Ω l0 l1) :
    T.dom l1 = .One ∨ (l1 = Z ∧ T.dom l0 = .One) := by
  induction s generalizing l0 l1 with
  | Z => cases h
  | P a b c d ih0 ih1 ih2 ih3 =>
    rw [T.dom] at h
    split at h
    · cases hc : T.dom c with
      | Zero =>
        rw [hc] at h
        cases hb : T.dom b with
        | Zero =>
          rw [hb] at h
          cases ha : T.dom a with
          | Zero => rw [ha] at h; cases h
          | One => rw [ha] at h; cases h; exact Or.inr ⟨rfl, ha⟩
          | ω => rw [ha] at h; cases h
          | Ω m0 m1 => rw [ha] at h; cases h; exact ih0 _ _ ha
        | One => rw [hb] at h; cases h; exact Or.inl hb
        | ω => rw [hb] at h; cases h
        | Ω m0 m1 =>
          rw [hb] at h
          change (if P a b Z Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) = Dom.Ω l0 l1 at h
          split at h
          · cases h
          · cases h; exact ih1 _ _ hb
      | One => rw [hc] at h; cases h
      | ω => rw [hc] at h; cases h
      | Ω m0 m1 =>
        rw [hc] at h
        change (if P a b c Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) = Dom.Ω l0 l1 at h
        split at h
        · cases h
        · cases h; exact ih2 _ _ hc
    · exact ih3 _ _ h

theorem T.add_P (a b c d t : T) : P a b c d + t = P a b c (d + t) := by
  cases t with
  | Z => cases d with | Z => rfl | P d0 d1 d2 d3 => rfl
  | P t0 t1 t2 t3 => rfl

theorem T.mul_principal_cases (a b c t : T) :
    T.mul (P a b c Z) t = Z ∨ ∃ r, T.mul (P a b c Z) t = P a b c r := by
  induction t with
  | Z => exact Or.inl rfl
  | P t0 t1 t2 t3 _ _ _ ih =>
    rw [T.mul]
    cases ih with
    | inl heq => rw [heq]; exact Or.inr ⟨Z, rfl⟩
    | inr hex =>
      cases hex with
      | intro r hr => rw [hr, T.add_P]; exact Or.inr ⟨r + P a b c Z, rfl⟩

theorem T.mul_lt_P (a b c e t : T) (h : c < e) : T.mul (P a b c Z) t < P a b e Z := by
  cases T.mul_principal_cases a b c t with
  | inl heq => rw [heq]; exact T.lt.Z_lt_P a b e Z
  | inr hex =>
    cases hex with
    | intro r hr => rw [hr]; exact T.lt.p_third _ _ _ _ _ _ h

theorem T.iter_lt (F : T → T) (t k : T) (hZ : Z < k) (hF : ∀ x, F x < k) :
    T.iter F t < k := by
  cases t with
  | Z => exact hZ
  | P t0 t1 t2 t3 => exact hF (T.iter F t3)

theorem T.fund_lt_of_domain (s t : T) (hne : s ≠ Z)
    (ht : ∀ l0 l1, T.dom s = .Ω l0 l1 → t < P l0 l1 Z Z) : T.fund s t < s := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
    cases s with
    | Z => exact False.elim (hne rfl)
    | P a b c d =>
      have boundedIteration (v l0 l1 : T) (hv : T.size v < T.size (P a b c d))
          (hd : T.dom v = .Ω l0 l1) :
          (if T.dom l1 = .One then
            T.iter (fun x => P l0 (T.fund l1 Z) (T.fund v x) Z) t
           else T.iter (fun x => P (T.fund l0 Z) (T.fund v x) Z Z) t) < P l0 l1 Z Z := by
        by_cases hl1 : T.dom l1 = .One
        · rw [ite_eq_left hl1]
          apply T.iter_lt _ _ _ (T.lt.Z_lt_P _ _ _ _)
          intro x
          apply T.lt.p_second
          apply ih l1 (Nat.lt_trans (T.dom_omega_size v l0 l1 hd).2 hv) Z
          · intro hz; rw [hz] at hl1; cases hl1
          · intro m0 m1 hm; exact T.lt.Z_lt_P _ _ _ _
        · rw [ite_eq_right hl1]
          have hl0 : T.dom l0 = .One := by
            cases T.dom_omega_index_cases v l0 l1 hd with
            | inl h => exact False.elim (hl1 h)
            | inr h => exact h.2
          apply T.iter_lt _ _ _ (T.lt.Z_lt_P _ _ _ _)
          intro x
          apply T.lt.p_first
          apply ih l0 (Nat.lt_trans (T.dom_omega_size v l0 l1 hd).1 hv) Z
          · intro hz; rw [hz] at hl0; cases hl0
          · intro m0 m1 hm; exact T.lt.Z_lt_P _ _ _ _
      by_cases hdZ : d = Z
      · cases hdZ
        rw [T.fund, ite_eq_left rfl]
        cases hc : T.dom c with
        | Zero =>
          have hcZ := T.dom_eq_zero c hc
          cases hcZ
          cases hb : T.dom b with
          | Zero =>
            have hbZ := T.dom_eq_zero b hb
            cases hbZ
            cases ha : T.dom a with
            | Zero => exact T.lt.Z_lt_P _ _ _ _
            | One =>
              apply ht a Z
              change (match T.dom a with
                | .Zero => Dom.One | .One => Dom.Ω a Z | .ω => Dom.ω | .Ω x y => Dom.Ω x y) = _
              rw [ha]
            | ω =>
              apply T.lt.p_first
              apply ih a (T.size_lt_size_P_first _ _ _ _) t
              · intro hz; rw [hz] at ha; cases ha
              · intro x y h; rw [ha] at h; cases h
            | Ω l0 l1 =>
              apply T.lt.p_first
              apply ih a (T.size_lt_size_P_first _ _ _ _) t
              · intro hz; rw [hz] at ha; cases ha
              · intro x y h
                apply ht x y
                change (match T.dom a with
                  | .Zero => Dom.One | .One => Dom.Ω a Z | .ω => Dom.ω | .Ω x y => Dom.Ω x y) = _
                rw [h]
          | One =>
            apply ht a b
            rw [T.dom, ite_eq_left rfl, show T.dom Z = .Zero from rfl, hb]
          | ω =>
            apply T.lt.p_second
            apply ih b (T.size_lt_size_P_second _ _ _ _) t
            · intro hz; rw [hz] at hb; cases hb
            · intro x y h; rw [hb] at h; cases h
          | Ω l0 l1 =>
            change (if P a b Z Z < P l0 l1 Z Z then
              if T.dom l1 = .One then
                P a (T.fund b (T.iter (fun x => P l0 (T.fund l1 Z) (T.fund b x) Z) t)) Z Z
              else P a (T.fund b (T.iter (fun x => P (T.fund l0 Z) (T.fund b x) Z Z) t)) Z Z
              else P a (T.fund b t) Z Z) < P a b Z Z
            by_cases hcollapse : P a b Z Z < P l0 l1 Z Z
            · rw [ite_eq_left hcollapse]
              have hbound := boundedIteration b l0 l1 (T.size_lt_size_P_second _ _ _ _) hb
              have hbne : b ≠ Z := by intro hz; rw [hz] at hb; cases hb
              have harg : ∀ u, u < P l0 l1 Z Z → T.fund b u < b := by
                intro u hu
                apply ih b (T.size_lt_size_P_second _ _ _ _) u hbne
                intro x y h; rw [hb] at h; cases h; exact hu
              by_cases hl : T.dom l1 = .One
              · rw [ite_eq_left hl] at hbound ⊢
                exact T.lt.p_second _ _ _ _ _ _ _ (harg _ hbound)
              · rw [ite_eq_right hl] at hbound ⊢
                exact T.lt.p_second _ _ _ _ _ _ _ (harg _ hbound)
            · rw [ite_eq_right hcollapse]
              apply T.lt.p_second
              apply ih b (T.size_lt_size_P_second _ _ _ _) t
              · intro hz; rw [hz] at hb; cases hb
              · intro x y h
                rw [hb] at h
                cases h
                apply ht l0 l1
                rw [T.dom, ite_eq_left rfl, show T.dom Z = .Zero from rfl, hb]
                exact ite_eq_right hcollapse
        | One =>
          apply T.mul_lt_P
          apply ih c (T.size_lt_size_P_third _ _ _ _) Z
          · intro hz; rw [hz] at hc; cases hc
          · intro x y h; exact T.lt.Z_lt_P _ _ _ _
        | ω =>
          apply T.lt.p_third
          apply ih c (T.size_lt_size_P_third _ _ _ _) t
          · intro hz; rw [hz] at hc; cases hc
          · intro x y h; rw [hc] at h; cases h
        | Ω l0 l1 =>
          change (if P a b c Z < P l0 l1 Z Z then
            if T.dom l1 = .One then
              P a b (T.fund c (T.iter (fun x => P l0 (T.fund l1 Z) (T.fund c x) Z) t)) Z
            else P a b (T.fund c (T.iter (fun x => P (T.fund l0 Z) (T.fund c x) Z Z) t)) Z
            else P a b (T.fund c t) Z) < P a b c Z
          by_cases hcollapse : P a b c Z < P l0 l1 Z Z
          · rw [ite_eq_left hcollapse]
            have hbound := boundedIteration c l0 l1 (T.size_lt_size_P_third _ _ _ _) hc
            have hcne : c ≠ Z := by intro hz; rw [hz] at hc; cases hc
            have harg : ∀ u, u < P l0 l1 Z Z → T.fund c u < c := by
              intro u hu
              apply ih c (T.size_lt_size_P_third _ _ _ _) u hcne
              intro x y h; rw [hc] at h; cases h; exact hu
            by_cases hl : T.dom l1 = .One
            · rw [ite_eq_left hl] at hbound ⊢
              exact T.lt.p_third _ _ _ _ _ _ (harg _ hbound)
            · rw [ite_eq_right hl] at hbound ⊢
              exact T.lt.p_third _ _ _ _ _ _ (harg _ hbound)
          · rw [ite_eq_right hcollapse]
            apply T.lt.p_third
            apply ih c (T.size_lt_size_P_third _ _ _ _) t
            · intro hz; rw [hz] at hc; cases hc
            · intro x y h
              rw [hc] at h
              cases h
              apply ht l0 l1
              rw [T.dom, ite_eq_left rfl, hc]
              exact ite_eq_right hcollapse
      · rw [T.fund, ite_eq_right hdZ]
        apply T.lt.p_fourth
        apply ih d (T.size_lt_size_P_fourth _ _ _ _) t hdZ
        intro x y h
        apply ht x y
        rw [T.dom, ite_eq_right hdZ]
        exact h

theorem T.ofNat_lt_index (n : Nat) (l0 l1 : T) (hne : l0 ≠ Z ∨ l1 ≠ Z) :
    T.ofNat n < P l0 l1 Z Z := by
  cases n with
  | zero => exact T.lt.Z_lt_P _ _ _ _
  | succ n =>
    cases hne with
    | inl h0 =>
      cases l0 with
      | Z => exact False.elim (h0 rfl)
      | P a b c d => exact T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)
    | inr h1 =>
      cases l0 with
      | Z =>
        cases l1 with
        | Z => exact False.elim (h1 rfl)
        | P a b c d => exact T.lt.p_second _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)
      | P a b c d => exact T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)

theorem T.ofNat_in_domain (s : T) (n : Nat) :
    ∀ l0 l1, T.dom s = .Ω l0 l1 → T.ofNat n < P l0 l1 Z Z := by
  intro l0 l1 hd
  apply T.ofNat_lt_index
  cases T.dom_omega_index_cases s l0 l1 hd with
  | inl h1 =>
    apply Or.inr
    intro hz
    rw [hz] at h1
    cases h1
  | inr h0 =>
    apply Or.inl
    intro hz
    have h1 := h0.2
    rw [hz] at h1
    cases h1

theorem T.fund_ofNat_lt (s : T) (n : Nat) (hne : s ≠ Z) : T.fund s (T.ofNat n) < s :=
  T.fund_lt_of_domain s (T.ofNat n) hne (T.ofNat_in_domain s n)

theorem T.OT_lt_first_uncountable (s : T) (hs : T.isOT s) :
    s < P Z (P Z Z Z Z) Z Z := by
  induction hs with
  | base n => exact T.lt.p_second _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)
  | step s hs n ih =>
    by_cases hz : s = Z
    · rw [hz, T.fund_Z]
      exact T.lt.Z_lt_P _ _ _ _
    · exact T.lt_trans _ _ _ (T.fund_ofNat_lt s n hz) ih
