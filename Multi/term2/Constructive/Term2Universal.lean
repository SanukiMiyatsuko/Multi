import Multi.term2.Constructive.Term2Brackets

namespace T.Constructive

open T

abbrev Universal (s : T.NF) : Prop := reduction.Universal s

theorem universal_stage {s : T.NF} (hs : Universal s) : Stage Universal s :=
  (reduction.universal_distinguished reduction_cofinal).stage reduction hs

theorem universal_of_stage_le {s t : T.NF} (hs : Universal s)
    (ht : Stage Universal t) (hle : t.1 ≤ s.1) : Universal t := by
  have hle' : reduction.Le t s := by
    cases hle with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr (Subtype.ext h)
  exact (reduction.universal_distinguished reduction_cofinal s hs t hle').mpr ht

theorem universal_fund {s t : T.NF} (hs : Universal s) (ht : Input Universal s t) :
    Universal ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩ :=
  universal_of_stage_le hs (stage_fund (universal_stage hs) ht)
    (Or.inl (fund_lt_of_input ht))

theorem universal_of_inputs {s : T.NF}
    (hchildren : ∀ (t : T.NF) (ht : Input Universal s t),
      Universal ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩)
    (hconvert : ∀ t, Input (Stage Universal) s t → Input Universal s t) : Universal s := by
  apply reduction.universal_of_closed reduction_cofinal
  · intro b hb
    cases hb with
    | intro t ht =>
      have heq : b = ⟨T.fund s.1 t.1, fund_isNF_of_input ht.1⟩ := Subtype.ext ht.2
      rw [heq]
      exact hchildren t ht.1
  · intro b hb
    cases hb with
    | intro t ht => exact ⟨t, hconvert t ht.1, ht.2⟩

theorem universal_nonomega {s : T.NF} (hd : ∀ l, T.dom s.1 ≠ .Ω l)
    (hchildren : ∀ (t : T.NF) (ht : Input Universal s t),
      Universal ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩) : Universal s :=
  universal_of_inputs hchildren (fun _ ht => (input_nonomega hd).mp ht)

theorem universal_zero : Universal ⟨Z, T.isNF.z⟩ := by
  apply universal_nonomega (fun l h => by cases h)
  intro t ht
  exact False.elim ht

theorem universal_add_one {s : T.NF} (hs : Universal s) :
    Universal ⟨s.1 + P Z Z Z, T.add_one_isNF s.1 s.2⟩ := by
  apply universal_nonomega
  · intro l h
    rw [T.dom_add_one] at h
    cases h
  · intro t ht
    have heq : (⟨T.fund (s.1 + P Z Z Z) t.1, fund_isNF_of_input ht⟩ : T.NF) = s :=
      Subtype.ext (T.fund_add_one s.1 t.1)
    rw [heq]
    exact hs

theorem universal_with_domain_witness {s r : T.NF} (hr : Universal r)
    (hd : T.dom s.1 = T.dom r.1)
    (hchildren : ∀ (t : T.NF) (ht : Input Universal s t),
      Universal ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩) : Universal s := by
  apply universal_of_inputs hchildren
  intro t ht
  have htR : Input (Stage Universal) r t := by
    unfold Input at ht ⊢
    rw [hd] at ht
    exact ht
  cases hsD : T.dom s.1 with
  | Zero => unfold Input at ht ⊢; rw [hsD] at ht ⊢; exact ht
  | One => unfold Input at ht ⊢; rw [hsD] at ht ⊢; exact ht
  | ω => unfold Input at ht ⊢; rw [hsD] at ht ⊢; exact ht
  | Ω l =>
    have hrD : T.dom r.1 = .Ω l := hd.symm.trans hsD
    have htr := input_lt_of_omega htR hrD
    unfold Input at ht ⊢
    rw [hsD] at ht ⊢
    refine ⟨ht.1, ?_⟩
    cases ht.2 with
    | inl htS => exact Or.inl (universal_of_stage_le hr htS (Or.inl htr))
    | inr htEq => exact Or.inr htEq

/-- Below a successor index, every consulted parameter is below the preceding
index. This is the locality needed to construct the next distinguished set. -/
theorem input_below_successor_index {X Y : T.NF → Prop} (a : T)
    (hlocal : ∀ z : T.NF, z.1 < P a Z Z → (X z ↔ Y z))
    {s t : T.NF} (hs : s.1 < P (a + P Z Z Z) Z Z) : Input X s t ↔ Input Y s t := by
  cases hd : T.dom s.1 with
  | Zero => unfold Input; rw [hd]
  | One => unfold Input; rw [hd]
  | ω => unfold Input; rw [hd]
  | Ω l =>
    have hl := dom_index_lt_of_below s.1 (a + P Z Z Z) l s.2 hd hs
    have hla := (T.fund_one_properties (a + P Z Z Z) (T.dom_add_one a)).2.2.1 l hl
    rw [T.fund_add_one] at hla
    have hidx := T.index_le_P l a Z Z hla
    unfold Input
    rw [hd]
    apply Iff.intro
    · intro ht
      refine ⟨ht.1, ?_⟩
      cases ht.2 with
      | inl htX => exact Or.inl ((hlocal t (lt_of_lt_of_le_thm T _ _ _ ht.1 hidx)).mp htX)
      | inr heq => exact Or.inr heq
    · intro ht
      refine ⟨ht.1, ?_⟩
      cases ht.2 with
      | inl htY => exact Or.inl ((hlocal t (lt_of_lt_of_le_thm T _ _ _ ht.1 hidx)).mpr htY)
      | inr heq => exact Or.inr heq

theorem stage_transport_below_successor_index {X Y : T.NF → Prop} (a : T)
    (hlocal : ∀ z : T.NF, z.1 < P a Z Z → (X z ↔ Y z))
    {s : T.NF} (h : Stage X s) :
    s.1 < P (a + P Z Z Z) Z Z → Stage Y s := by
  induction h with
  | intro s hchildren ih =>
    intro hs
    apply reduction.stage_intro
    intro b hb
    cases hb with
    | intro t ht =>
      have htX := (input_below_successor_index a hlocal hs).mpr ht.1
      have hbX : Step X b s := ⟨t, htX, ht.2⟩
      exact ih b hbX (T.lt_trans _ _ _ (reduction.step_lt hbX) hs)

theorem stage_local_below_successor_index {X Y : T.NF → Prop} (a : T)
    (hlocal : ∀ z : T.NF, z.1 < P a Z Z → (X z ↔ Y z))
    {s : T.NF} (hs : s.1 < P (a + P Z Z Z) Z Z) : Stage X s ↔ Stage Y s :=
  ⟨fun h => stage_transport_below_successor_index a hlocal h hs,
   fun h => stage_transport_below_successor_index a (fun z hz => (hlocal z hz).symm) h hs⟩

theorem universal_index_successor {a : T} {ha : T.isNF a}
    (h : Universal ⟨P a Z Z, T.isNF_index a ha⟩) :
    Universal ⟨P (a + P Z Z Z) Z Z, T.isNF_index _ (T.add_one_isNF a ha)⟩ := by
  let p : T.NF := ⟨P a Z Z, T.isNF_index a ha⟩
  let q : T.NF := ⟨P (a + P Z Z Z) Z Z, T.isNF_index _ (T.add_one_isNF a ha)⟩
  let X := reduction.Prefix Universal p
  let Y := Stage X
  have hX : reduction.Distinguished X :=
    (reduction.universal_distinguished reduction_cofinal).prefix reduction p
  have hpX : X p := ⟨h, reduction.le_refl p⟩
  have hpY : Y p := hX.stage reduction hpX
  have hlocal : ∀ z : T.NF, z.1 < P a Z Z → (X z ↔ Y z) :=
    fun z hz => hX p hpX z (Or.inl hz)
  have hbelow : ∀ z, reduction.lt z q → (Y z ↔ Stage Y z) :=
    fun z hz => stage_local_below_successor_index a hlocal hz
  have hq : Stage Y q := by
    apply stage_intro
    intro t ht
    have hd : T.dom q.1 = .Ω (a + P Z Z Z) := by
      change T.dom (P (a + P Z Z Z) Z Z) = _
      rw [dom_index, T.dom_add_one]
    have hf : T.fund q.1 t.1 = t.1 := by
      change T.fund (P (a + P Z Z Z) Z Z) t.1 = t.1
      rw [fund_index, T.dom_add_one]
    have heq : (⟨T.fund q.1 t.1, fund_isNF_of_input ht⟩ : T.NF) = t := Subtype.ext hf
    rw [heq]
    unfold Input at ht
    rw [hd] at ht
    apply (hbelow t ht.1).mp
    cases ht.2 with
    | inl htY => exact htY
    | inr htEq =>
      rw [T.fund_add_one] at htEq
      have heq : t = p := Subtype.ext htEq
      rw [heq]
      exact hpY
  exact ⟨reduction.Prefix (Stage Y) q, reduction.distinguished_extension hbelow,
    hq, reduction.le_refl q⟩

theorem universal_index {a : T.NF} (ha : Universal a) :
    Universal ⟨P a.1 Z Z, T.isNF_index a.1 a.2⟩ := by
  have hacc := reduction.universal_acc reduction_cofinal ha
  induction hacc with
  | intro a hchildren ih =>
    let ia : T.NF := ⟨P a.1 Z Z, T.isNF_index a.1 a.2⟩
    have liftLimit (hd : T.dom ia.1 = T.dom a.1)
        (hf : ∀ t, T.fund ia.1 t = P (T.fund a.1 t) Z Z) : Universal ia := by
      apply universal_with_domain_witness ha hd
      intro t ht
      have htA : Input Universal a t := by
        unfold Input at ht ⊢
        rw [hd] at ht
        exact ht
      have hc := universal_fund ha htA
      have hi := ih ⟨T.fund a.1 t.1, fund_isNF_of_input htA⟩
        ⟨hc, fund_lt_of_input htA⟩ hc
      have heq : (⟨T.fund ia.1 t.1, fund_isNF_of_input ht⟩ : T.NF) =
          ⟨P (T.fund a.1 t.1) Z Z, T.isNF_index _ (fund_isNF_of_input htA)⟩ :=
        Subtype.ext (hf t.1)
      rw [heq]
      exact hi
    cases hd : T.dom a.1 with
    | Zero =>
      have haz := T.dom_eq_zero a.1 hd
      have heq : ia = ⟨Z + P Z Z Z, T.add_one_isNF Z T.isNF.z⟩ := by
        apply Subtype.ext
        change P a.1 Z Z = P Z Z Z
        rw [haz]
      change Universal ia
      rw [heq]
      exact universal_add_one universal_zero
    | One =>
      have ht : Input Universal a ⟨Z, T.isNF.z⟩ := by unfold Input; rw [hd]
      have hp := universal_fund ha ht
      have hi := ih ⟨T.fund a.1 Z, fund_isNF_of_input ht⟩ ⟨hp, fund_lt_of_input ht⟩ hp
      have hsucc := universal_index_successor (ha := fund_isNF_of_input ht) hi
      have heq : (⟨P (T.fund a.1 Z + P Z Z Z) Z Z,
          T.isNF_index _ (T.add_one_isNF _ (fund_isNF_of_input ht))⟩ : T.NF) = ia :=
        Subtype.ext (congrArg (fun v => P v Z Z) (T.fund_one_properties a.1 hd).2.1.symm)
      rw [heq] at hsucc
      exact hsucc
    | ω =>
      apply liftLimit
      · change T.dom (P a.1 Z Z) = T.dom a.1
        rw [dom_index, hd]
      · intro t
        change T.fund (P a.1 Z Z) t = P (T.fund a.1 t) Z Z
        rw [fund_index, hd]
    | Ω l =>
      apply liftLimit
      · change T.dom (P a.1 Z Z) = T.dom a.1
        rw [dom_index, hd]
      · intro t
        change T.fund (P a.1 Z Z) t = P (T.fund a.1 t) Z Z
        rw [fund_index, hd]

theorem universal_of_index {a : T} {ha : T.isNF a}
    (h : Universal ⟨P a Z Z, T.isNF_index a ha⟩) : Universal ⟨a, ha⟩ :=
  universal_of_stage_le h (stage_of_index (universal_stage h)) (Or.inl (T.first_lt a Z Z))

theorem universal_domain_index {s : T.NF} (hs : Universal s) {l : T}
    (hd : T.dom s.1 = .Ω l) :
    Universal ⟨l, T.dom_omega_index_isNF s.1 l s.2 hd⟩ := by
  have hlNF := T.dom_omega_index_isNF s.1 l s.2 hd
  have hlone := T.dom_omega_index_one s.1 l hd
  have hlpNF := T.fund_one_isNF l hlNF hlone Z
  have hlne : l ≠ Z := by intro h; rw [h] at hlone; cases hlone
  have hlp : T.fund l Z < l := T.fund_ofNat_lt l 0 hlne
  let t : T.NF := ⟨P (T.fund l Z) Z Z, T.isNF_index _ hlpNF⟩
  have ht : Input Universal s t := by
    unfold Input
    rw [hd]
    exact ⟨T.lt.p_first _ _ _ _ _ _ hlp, Or.inr rfl⟩
  have hc := universal_fund hs ht
  have htStage : Stage Universal t := stage_of_fund_omega Universal s.1 l t.1 s.2 hd t.2
    (input_bound ht l hd) (universal_stage hc)
  have htU := universal_of_stage_le hc htStage
    (T.input_le_fund_omega s.1 l s.2 hd t.1 (input_bound ht l hd))
  have hi := universal_index_successor (ha := hlpNF) htU
  have heq : (⟨P (T.fund l Z + P Z Z Z) Z Z,
      T.isNF_index _ (T.add_one_isNF _ hlpNF)⟩ : T.NF) = ⟨P l Z Z, T.isNF_index l hlNF⟩ :=
    Subtype.ext (congrArg (fun v => P v Z Z) (T.fund_one_properties l hlone).2.1.symm)
  rw [heq] at hi
  exact universal_of_index (ha := hlNF) hi

theorem universal_tail {c : T.NF} (hc : Universal c) :
    ∀ (a b : T) (hs : T.isNF (P a b c.1)),
    Universal ⟨P a b Z, T.head_isNF _ hs⟩ → Universal ⟨P a b c.1, hs⟩ := by
  have hacc := reduction.universal_acc reduction_cofinal hc
  induction hacc with
  | intro c hchildren ih =>
    intro a b hs hh
    by_cases hcZ : c.1 = Z
    · have heq : (⟨P a b c.1, hs⟩ : T.NF) = ⟨P a b Z, T.head_isNF _ hs⟩ :=
        Subtype.ext (congrArg (P a b) hcZ)
      rw [heq]
      exact hh
    · have hd : T.dom (P a b c.1) = T.dom c.1 := by rw [T.dom, ite_eq_right hcZ]
      apply universal_with_domain_witness hc hd
      intro t ht
      have htC : Input Universal c t := by
        unfold Input at ht ⊢
        rw [hd] at ht
        exact ht
      have hct := universal_fund hc htC
      have hnf := T.isNF_replace_tail a b c.1 (T.fund c.1 t.1) hs (fund_isNF_of_input htC)
        (Or.inl (fund_lt_of_input htC))
      have hu := ih ⟨T.fund c.1 t.1, fund_isNF_of_input htC⟩
        ⟨hct, fund_lt_of_input htC⟩ hct a b hnf hh
      have heq : (⟨T.fund (P a b c.1) t.1, fund_isNF_of_input ht⟩ : T.NF) =
          ⟨P a b (T.fund c.1 t.1), hnf⟩ := Subtype.ext (fund_nonzero_tail_eq a b c.1 t.1 hcZ)
      rw [heq]
      exact hu

theorem universal_mul_principal (a b : T) (h : T.isNF (P a b Z))
    (hu : Universal ⟨P a b Z, h⟩) (t : T) :
    Universal ⟨T.mul (P a b Z) t, T.mul_principal_isNF a b t h⟩ := by
  induction t with
  | Z => exact universal_zero
  | P t0 t1 t2 _ _ ih =>
    have heq : T.mul (P a b Z) (P t0 t1 t2) = P a b (T.mul (P a b Z) t2) := by
      rw [T.mul, T.mul_principal_add]
    have hnf : T.isNF (P a b (T.mul (P a b Z) t2)) := by
      rw [← heq]
      exact T.mul_principal_isNF a b _ h
    have hh := universal_tail ih a b hnf hu
    have hsub : (⟨T.mul (P a b Z) (P t0 t1 t2), T.mul_principal_isNF a b _ h⟩ : T.NF) =
        ⟨P a b (T.mul (P a b Z) t2), hnf⟩ := Subtype.ext heq
    rw [hsub]
    exact hh

end T.Constructive
