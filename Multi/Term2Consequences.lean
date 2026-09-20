import Multi.Term2Syntax

def T.OT := { s : T // T.isOT s }

theorem T.OT_characterization_of_wellFounded_and_fundamental_properties
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1)
    (hclosed : ∀ s, T.isNF s → s < P (P Z Z Z) Z Z →
      ∀ n, T.isNF (T.fund s (T.ofNat n)))
    (s : T) :
    T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z := by
  apply Iff.intro
  · intro hs
    induction hs with
    | base n => exact And.intro (T.base_isNF n) (T.base_lt_omega_one n)
    | step t ht n ih =>
      apply And.intro (hclosed t ih.1 ih.2 n)
      by_cases heq : t = Z
      · rw [heq, T.fund_Z]
        exact T.lt.Z_lt_P (P Z Z Z) Z Z
      · exact T.lt_trans _ _ _ (T.fund_ofNat_lt t n heq) ih.2
  · intro hs
    have downward : ∀ x : T.NF, T.isOT x.1 → x.1 < P (P Z Z Z) Z Z →
        ∀ r, T.isNF r → r ≤ x.1 → T.isOT r := by
      intro x
      induction x using hwf.induction with
      | h x ih =>
        intro hx hxbound r hr hrx
        cases hrx with
        | inr heq =>
          cases heq
          exact hx
        | inl hrx =>
          have hne : x.1 ≠ Z := by
            intro heq
            rw [heq] at hrx
            exact lt_Z_inv r hrx
          cases T.fund_cofinal_below_omega_one x.1 r x.2 hr hxbound hrx with
          | intro n hn =>
            let y : T.NF := ⟨T.fund x.1 (T.ofNat n), hclosed x.1 x.2 hxbound n⟩
            have hyx : y.1 < x.1 := T.fund_ofNat_lt x.1 n hne
            exact ih y hyx (T.isOT.step x.1 hx n)
              (T.lt_trans _ _ _ hyx hxbound) r hr hn
    cases T.base_cofinal_below_omega_one s hs.2 with
    | intro n hn =>
      exact downward ⟨P Z (T.LF n) Z, T.base_isNF n⟩ (T.isOT.base n)
        (T.base_lt_omega_one n) s hs.1 (Or.inl hn)

/-- A constructive proof of well-foundedness suffices for the characterization. -/
theorem T.OT_is_NF_of_wellFounded
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1)
    (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z := by
  exact T.OT_characterization_of_wellFounded_and_fundamental_properties hwf
    (fun t ht _ n => T.fund_ofNat_isNF t ht n) s

theorem T.OT_wellFounded_of_NF_wellFounded
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1) :
    WellFounded fun x y : T.OT => x.1 < y.1 := by
  let toNF : T.OT → T.NF := fun x => ⟨x.1, ((T.OT_is_NF_of_wellFounded hwf x.1).mp x.2).1⟩
  exact InvImage.wf toNF hwf

