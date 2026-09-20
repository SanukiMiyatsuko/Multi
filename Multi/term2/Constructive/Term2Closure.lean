import Multi.term2.Constructive.Term2Universal

namespace T.Constructive

open T

theorem collapsing_iterate_isNF (a b l : T) (hs : T.isNF (P a b Z))
    (hd : T.dom b = .Ω l) (hal : a < l) (n : Nat) :
    T.isNF (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n)) := by
  cases n with
  | zero => exact T.isNF.z
  | succ n =>
    have hb := (T.isNF_components a b Z hs).2.1
    have hlNF := T.dom_omega_index_isNF b l hb hd
    have hlone := T.dom_omega_index_one b l hd
    have hlpNF := T.fund_one_isNF l hlNF hlone Z
    have hap := (T.fund_one_properties l hlone).2.2.1 a hal
    have hnf := T.fund_collapsing_principal_isNF a b l hs hd hal n
    rw [T.fund, ite_eq_left rfl, hd] at hnf
    change T.isNF (if a < l then P a
      (T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n))) Z
      else P a (T.fund b (T.ofNat n)) Z) at hnf
    rw [ite_eq_left hal] at hnf
    cases hnf with
    | p _ _ _ ha hbn hz hreg hhead =>
      exact T.isNF.p _ _ Z hlpNF hbn T.isNF.z
        (T.GBound_index_mono _ a (T.fund l Z) _ hap hreg) (T.Z_le _)

theorem universal_principal {b : T.NF} (hb : Universal b) :
    ∀ (a : T) (ha : T.isNF a), Universal ⟨a, ha⟩ →
    ∀ hs : T.isNF (P a b.1 Z), Universal ⟨P a b.1 Z, hs⟩ := by
  have hacc := reduction.universal_acc reduction_cofinal hb
  induction hacc with
  | intro b hchildren ih =>
    intro a ha haU hs
    let s : T.NF := ⟨P a b.1 Z, hs⟩
    have liftDomain (hd : T.dom s.1 = T.dom b.1)
        (hf : ∀ t, T.fund s.1 t = P a (T.fund b.1 t) Z) : Universal s := by
      apply universal_with_domain_witness hb hd
      intro t ht
      have htB : Input Universal b t := by
        unfold Input at ht ⊢
        rw [hd] at ht
        exact ht
      have hbt := universal_fund hb htB
      have hnf : T.isNF (P a (T.fund b.1 t.1) Z) := by
        rw [← hf t.1]
        exact fund_isNF_of_input ht
      have hu := ih ⟨T.fund b.1 t.1, fund_isNF_of_input htB⟩
        ⟨hbt, fund_lt_of_input htB⟩ hbt a ha haU hnf
      have heq : (⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩ : T.NF) =
          ⟨P a (T.fund b.1 t.1) Z, hnf⟩ := Subtype.ext (hf t.1)
      rw [heq]
      exact hu
    cases hd : T.dom b.1 with
    | Zero =>
      have hbZ := T.dom_eq_zero b.1 hd
      have heq : s = ⟨P a Z Z, T.isNF_index a ha⟩ :=
        Subtype.ext (congrArg (fun v => P a v Z) hbZ)
      change Universal s
      rw [heq]
      exact universal_index haU
    | One =>
      have htB : Input Universal b ⟨Z, T.isNF.z⟩ := by unfold Input; rw [hd]
      have hbt := universal_fund hb htB
      have hreg : T.GBound a b.1 b.1 := by cases hs with | p _ _ _ _ _ _ h _ => exact h
      have hnf : T.isNF (P a (T.fund b.1 Z) Z) :=
        T.isNF.p a _ Z ha (fund_isNF_of_input htB) T.isNF.z
          (T.fund_one_regular a b.1 b.2 hd hreg) (T.Z_le _)
      have hu := ih ⟨T.fund b.1 Z, fund_isNF_of_input htB⟩
        ⟨hbt, fund_lt_of_input htB⟩ hbt a ha haU hnf
      have hdS : T.dom s.1 = .ω := by
        change T.dom (P a b.1 Z) = .ω
        rw [T.dom, ite_eq_left rfl, hd]
      apply universal_nonomega (fun l h => by rw [hdS] at h; cases h)
      intro t ht
      have hf : T.fund s.1 t.1 = T.mul (P a (T.fund b.1 Z) Z) t.1 := by
        change T.fund (P a b.1 Z) t.1 = _
        rw [T.fund, ite_eq_left rfl, hd]
      have hm := universal_mul_principal a (T.fund b.1 Z) hnf hu t.1
      have heq : (⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩ : T.NF) =
          ⟨T.mul (P a (T.fund b.1 Z) Z) t.1, T.mul_principal_isNF _ _ _ hnf⟩ := Subtype.ext hf
      rw [heq]
      exact hm
    | ω =>
      apply liftDomain
      · change T.dom (P a b.1 Z) = T.dom b.1
        rw [T.dom, ite_eq_left rfl, hd]
      · intro t
        exact fund_principal_countable a b.1 t hd
    | Ω l =>
      by_cases hal : a < l
      · have hlNF := T.dom_omega_index_isNF b.1 l b.2 hd
        have hlone := T.dom_omega_index_one b.1 l hd
        have hlU := universal_domain_index hb hd
        have hlInput : Input Universal ⟨l, hlNF⟩ ⟨Z, T.isNF.z⟩ := by unfold Input; rw [hlone]
        have hlpU := universal_fund hlU hlInput
        have hlpNF := fund_isNF_of_input hlInput
        have hlne : l ≠ Z := by intro h; rw [h] at hlone; cases hlone
        have hlp := T.fund_ofNat_lt l 0 hlne
        let F := fun x => P (T.fund l Z) (T.fund b.1 x) Z
        let xs := fun n => T.iter F (T.ofNat n)
        have hxsNF : ∀ n, T.isNF (xs n) := collapsing_iterate_isNF a b.1 l hs hd hal
        have hxsBound : ∀ n, xs n < P l Z Z := by
          intro n
          cases n with
          | zero => exact T.lt.Z_lt_P l Z Z
          | succ n => exact T.lt.p_first _ _ _ _ _ _ hlp
        have inputX (n : Nat) (hn : Universal ⟨xs n, hxsNF n⟩) :
            Input Universal b ⟨xs n, hxsNF n⟩ := by
          unfold Input
          rw [hd]
          exact ⟨hxsBound n, Or.inl hn⟩
        have hxsU : ∀ n, Universal ⟨xs n, hxsNF n⟩ := by
          intro n
          induction n with
          | zero => exact universal_zero
          | succ n hn =>
            have ht := inputX n hn
            have hbt := universal_fund hb ht
            exact ih ⟨T.fund b.1 (xs n), fund_isNF_of_input ht⟩
              ⟨hbt, fund_lt_of_input ht⟩ hbt (T.fund l Z) hlpNF hlpU (hxsNF (n + 1))
        have hdS : T.dom s.1 = .ω := by
          change T.dom (P a b.1 Z) = .ω
          rw [T.dom, ite_eq_left rfl, hd]
          exact ite_eq_left hal
        apply universal_nonomega (fun m h => by rw [hdS] at h; cases h)
        intro t ht
        have ht' := ht
        unfold Input at ht'
        rw [hdS] at ht'
        cases ht' with
        | intro n htn =>
          have hn := inputX n (hxsU n)
          have hbn := universal_fund hb hn
          have hf : T.fund s.1 t.1 = P a (T.fund b.1 (xs n)) Z := by
            change T.fund (P a b.1 Z) t.1 = _
            rw [htn, T.fund, ite_eq_left rfl, hd]
            exact ite_eq_left hal
          have hnf : T.isNF (P a (T.fund b.1 (xs n)) Z) := by
            rw [← hf]
            exact fund_isNF_of_input ht
          have hu := ih ⟨T.fund b.1 (xs n), fund_isNF_of_input hn⟩
            ⟨hbn, fund_lt_of_input hn⟩ hbn a ha haU hnf
          have heq : (⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩ : T.NF) =
              ⟨P a (T.fund b.1 (xs n)) Z, hnf⟩ := Subtype.ext hf
          rw [heq]
          exact hu
      · have hla := T.le_of_not_lt a l hal
        apply liftDomain
        · exact (dom_principal_uncollapsed a b.1 l hd hla).trans hd.symm
        · intro t
          exact fund_principal_uncollapsed a b.1 l t hd hla

theorem universal_all (s : T.NF) : Universal s := by
  cases s with
  | mk s hs =>
    induction hs with
    | z => exact universal_zero
    | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
      have hp : T.isNF (P a b Z) := T.isNF.p a b Z ha hb T.isNF.z hreg (T.Z_le _)
      have hu := universal_principal ih1 a ha ih0 hp
      exact universal_tail ih2 a b (T.isNF.p a b c ha hb hc hreg hhead) hu

theorem normalForms_wellFounded : WellFounded (fun a b : T.NF => a.1 < b.1) :=
  reduction.wellFounded_of_universal reduction_cofinal universal_all

end T.Constructive
