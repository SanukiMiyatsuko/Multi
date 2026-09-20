import Multi.term2.Constructive.Term2Commutation

namespace T.Constructive

open T

/-- A proof for a value between two consecutive sequence entries yields a
proof for the input selecting the lower entry. -/
theorem stage_of_omega_interval (X : T.NF → Prop) (s l t : T) (hs : T.isNF s)
    (hd : T.dom s = .Ω l) (ht : T.isNF t) (htBound : t < P l Z Z)
    (r : T.NF) (hr : Stage X r)
    (hlo : T.fund s t ≤ r.1) (hhi : r.1 < T.fund s (t + P Z Z Z)) :
    Stage X ⟨t, ht⟩ := by
  induction hr generalizing s l t with
  | intro r hchildren ih =>
    have below (v : T) (hv : T.isNF v) (hvBound : v < P l Z Z)
        (hlow : T.fund s v < r.1) (hupp : r.1 ≤ T.fund s (v + P Z Z Z)) :
        Stage X ⟨v, hv⟩ := by
      have hrne : r.1 ≠ Z := by intro h; rw [h] at hlow; exact lt_Z_inv _ hlow
      let ar : T.NF := ⟨anchor r.1, anchor_isNF r.1 r.2⟩
      have har : Input X r ar := anchor_input X r hrne
      let rc : T.NF := ⟨T.fund r.1 ar.1, fund_isNF_of_input har⟩
      have hstep : Step X rc r := ⟨ar, har, rfl⟩
      have hrc : rc.1 < r.1 := fund_lt_of_input har
      exact ih rc hstep s l v hs hd hv hvBound
        (fund_omega_bachmann s l v r.1 hd r.2 hlow hupp)
        (lt_of_lt_of_le_thm T rc.1 r.1 _ hrc hupp)
    cases hlo with
    | inl hlo => exact below t ht htBound hlo (Or.inl hhi)
    | inr heq =>
      have limitCase (h0 : T.dom t ≠ .Zero) (h1 : T.dom t ≠ .One) : Stage X ⟨t, ht⟩ := by
        have hp := fund_omega_commutation s l t hs hd ht htBound h0 h1
        have hdom : T.dom r.1 = T.dom t := (congrArg T.dom heq).symm.trans hp.1
        apply stage_intro
        intro z hz
        have hzR : Input X r z := by
          unfold Input at hz ⊢
          rw [hdom]
          exact hz
        let rc : T.NF := ⟨T.fund r.1 z.1, fund_isNF_of_input hzR⟩
        have hstep : Step X rc r := ⟨z, hzR, rfl⟩
        have hzNF := fund_isNF_of_input hz
        have hzt : T.fund t z.1 < t := fund_lt_of_input hz
        have hcEq : rc.1 = T.fund s (T.fund t z.1) := by
          change T.fund r.1 z.1 = T.fund s (T.fund t z.1)
          rw [← heq]
          exact hp.2 z.1
        apply ih rc hstep s l (T.fund t z.1) hs hd hzNF
          (T.lt_trans _ _ _ hzt htBound)
        · exact Or.inr hcEq.symm
        · rw [hcEq]
          exact T.fund_omega_strict s l hd _ _ (T.lt_add_one _)
      cases htD : T.dom t with
      | Zero =>
        have htZ := T.dom_eq_zero t htD
        have hsub : (⟨t, ht⟩ : T.NF) = ⟨Z, T.isNF.z⟩ := Subtype.ext htZ
        rw [hsub]
        exact stage_zero X
      | One =>
        have htne : t ≠ Z := by intro h; rw [h] at htD; cases htD
        have hvNF := T.fund_one_isNF t ht htD Z
        have hvt : T.fund t Z < t := T.fund_ofNat_lt t 0 htne
        have htEq := (T.fund_one_properties t htD).2.1
        have hlow : T.fund s (T.fund t Z) < r.1 := by
          rw [← heq]
          exact T.fund_omega_strict s l hd _ _ hvt
        have hupp : r.1 ≤ T.fund s (T.fund t Z + P Z Z Z) := by
          rw [← htEq, heq]
          exact Or.inr rfl
        have hv := below (T.fund t Z) hvNF (T.lt_trans _ _ _ hvt htBound) hlow hupp
        have hplus := stage_add_one hv
        have hsub : (⟨T.fund t Z + P Z Z Z, T.add_one_isNF _ hvNF⟩ : T.NF) =
            ⟨t, ht⟩ := Subtype.ext htEq.symm
        rw [hsub] at hplus
        exact hplus
      | ω =>
        exact limitCase (fun h => by rw [htD] at h; cases h)
          (fun h => by rw [htD] at h; cases h)
      | Ω m =>
        exact limitCase (fun h => by rw [htD] at h; cases h)
          (fun h => by rw [htD] at h; cases h)

theorem stage_of_fund_omega (X : T.NF → Prop) (s l t : T) (hs : T.isNF s)
    (hd : T.dom s = .Ω l) (ht : T.isNF t) (htBound : t < P l Z Z)
    (h : Stage X ⟨T.fund s t, T.fund_omega_isNF s l t hs hd ht htBound⟩) :
    Stage X ⟨t, ht⟩ :=
  stage_of_omega_interval X s l t hs hd ht htBound _ h (Or.inr rfl)
    (T.fund_omega_strict s l hd _ _ (T.lt_add_one t))

theorem stage_index_inverse {X : T.NF → Prop} {s : T.NF} (hs : Stage X s) :
    ∀ (a : T) (ha : T.isNF a), s.1 = P a Z Z → Stage X ⟨a, ha⟩ := by
  induction hs with
  | intro s hchildren ih =>
    intro a ha heq
    have hsub : s = ⟨P a Z Z, T.isNF_index a ha⟩ := Subtype.ext heq
    cases hsub
    let aNF : T.NF := ⟨a, ha⟩
    let ia : T.NF := ⟨P a Z Z, T.isNF_index a ha⟩
    have liftLimit (hd : T.dom ia.1 = T.dom a)
        (hf : ∀ t, T.fund ia.1 t = P (T.fund a t) Z Z) : Stage X aNF := by
      apply stage_intro
      intro t ht
      have htI : Input X ia t := by
        unfold Input at ht ⊢
        rw [hd]
        exact ht
      let ic : T.NF := ⟨T.fund ia.1 t.1, fund_isNF_of_input htI⟩
      exact ih ic ⟨t, htI, rfl⟩ (T.fund a t.1) (fund_isNF_of_input ht) (hf t.1)
    cases hd : T.dom a with
    | Zero =>
      have haZ := T.dom_eq_zero a hd
      have heq : aNF = ⟨Z, T.isNF.z⟩ := Subtype.ext haZ
      change Stage X aNF
      rw [heq]
      exact stage_zero X
    | One =>
      have haNF := T.fund_one_isNF a ha hd Z
      have hane : a ≠ Z := by intro h; rw [h] at hd; cases hd
      have hpa : T.fund a Z < a := T.fund_ofNat_lt a 0 hane
      let ip : T.NF := ⟨P (T.fund a Z) Z Z, T.isNF_index _ haNF⟩
      have hInput : Input X ia ip := by
        unfold Input
        change (match T.dom (P a Z Z) with
          | .Zero => False | .One => ip.1 = Z
          | .ω => ∃ n, ip.1 = T.ofNat n
          | .Ω l => ip.1 < P l Z Z ∧ (X ip ∨ ip.1 = P (T.fund l Z) Z Z))
        rw [dom_index, hd]
        exact ⟨T.lt.p_first _ _ _ _ _ _ hpa, Or.inr rfl⟩
      have hfund : ip.1 = T.fund ia.1 ip.1 := by
        change ip.1 = T.fund (P a Z Z) ip.1
        rw [fund_index, hd]
      have hpStage := ih ip ⟨ip, hInput, hfund⟩ (T.fund a Z) haNF rfl
      have hplus := stage_add_one hpStage
      have heq : (⟨T.fund a Z + P Z Z Z, T.add_one_isNF _ haNF⟩ : T.NF) = aNF :=
        Subtype.ext (T.fund_one_properties a hd).2.1.symm
      rw [heq] at hplus
      exact hplus
    | ω =>
      apply liftLimit
      · change T.dom (P a Z Z) = T.dom a
        rw [dom_index, hd]
      · intro t
        change T.fund (P a Z Z) t = P (T.fund a t) Z Z
        rw [fund_index, hd]
    | Ω l =>
      apply liftLimit
      · change T.dom (P a Z Z) = T.dom a
        rw [dom_index, hd]
      · intro t
        change T.fund (P a Z Z) t = P (T.fund a t) Z Z
        rw [fund_index, hd]

theorem stage_of_index {X : T.NF → Prop} {a : T} {ha : T.isNF a}
    (h : Stage X ⟨P a Z Z, T.isNF_index a ha⟩) : Stage X ⟨a, ha⟩ :=
  stage_index_inverse h a ha rfl

end T.Constructive
