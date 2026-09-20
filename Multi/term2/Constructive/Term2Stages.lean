import Multi.term2.Term2Syntax
import Multi.Stages

namespace T.Constructive

open T

/-- The mandatory input at an uncountable domain records the preceding index. -/
def Input (X : T.NF → Prop) (s t : T.NF) : Prop :=
  match T.dom s.1 with
  | .Zero => False
  | .One => t.1 = Z
  | .ω => ∃ n : Nat, t.1 = T.ofNat n
  | .Ω l => t.1 < P l Z Z ∧ (X t ∨ t.1 = P (T.fund l Z) Z Z)

def Step (X : T.NF → Prop) (b a : T.NF) : Prop :=
  ∃ t : T.NF, Input X a t ∧ b.1 = T.fund a.1 t.1

theorem input_nonzero {X : T.NF → Prop} {s t : T.NF} (h : Input X s t) : s.1 ≠ Z := by
  intro hs
  unfold Input at h
  rw [hs] at h
  exact h

theorem input_bound {X : T.NF → Prop} {s t : T.NF} (h : Input X s t)
    (l : T) (hd : T.dom s.1 = .Ω l) : t.1 < P l Z Z := by
  unfold Input at h
  rw [hd] at h
  exact h.1

theorem fund_lt_of_input {X : T.NF → Prop} {s t : T.NF} (h : Input X s t) :
    T.fund s.1 t.1 < s.1 :=
  T.fund_lt_of_domain s.1 t.1 (input_nonzero h) (input_bound h)

theorem input_lt_of_omega {X : T.NF → Prop} {s t : T.NF} (h : Input X s t)
    {l : T} (hd : T.dom s.1 = .Ω l) : t.1 < s.1 :=
  lt_of_le_of_lt_thm T t.1 (T.fund s.1 t.1) s.1
    (T.input_le_fund_omega s.1 l s.2 hd t.1 (input_bound h l hd)) (fund_lt_of_input h)

theorem input_local {X Y : T.NF → Prop} {s t : T.NF}
    (h : ∀ z : T.NF, z.1 < s.1 → (X z ↔ Y z)) : Input X s t ↔ Input Y s t := by
  cases hd : T.dom s.1 with
  | Zero => unfold Input; rw [hd]
  | One => unfold Input; rw [hd]
  | ω => unfold Input; rw [hd]
  | Ω l =>
    apply Iff.intro
    · intro ht
      have hts := input_lt_of_omega ht hd
      unfold Input at ht ⊢
      rw [hd] at ht ⊢
      refine ⟨ht.1, ?_⟩
      cases ht.2 with
      | inl hX => exact Or.inl ((h t hts).mp hX)
      | inr heq => exact Or.inr heq
    · intro ht
      have hts := input_lt_of_omega ht hd
      unfold Input at ht ⊢
      rw [hd] at ht ⊢
      refine ⟨ht.1, ?_⟩
      cases ht.2 with
      | inl hY => exact Or.inl ((h t hts).mpr hY)
      | inr heq => exact Or.inr heq

def reduction : _root_.Constructive.Reduction T.NF where
  lt s t := s.1 < t.1
  trans := fun hst htu => T.lt_trans _ _ _ hst htu
  step := Step
  step_lt := by
    intro X a b h
    cases h with
    | intro t ht =>
      rw [ht.2]
      exact fund_lt_of_input ht.1
  step_local := by
    intro X Y a b h
    apply Iff.intro
    · intro hb
      cases hb with
      | intro t ht => exact ⟨t, (input_local h).mp ht.1, ht.2⟩
    · intro hb
      cases hb with
      | intro t ht => exact ⟨t, (input_local h).mpr ht.1, ht.2⟩

abbrev Stage (X : T.NF → Prop) (s : T.NF) : Prop := reduction.Stage X s

theorem fund_isNF_of_input {X : T.NF → Prop} {s t : T.NF} (h : Input X s t) :
    T.isNF (T.fund s.1 t.1) := by
  cases hd : T.dom s.1 with
  | Zero => unfold Input at h; rw [hd] at h; exact False.elim h
  | One => exact T.fund_one_isNF s.1 s.2 hd t.1
  | ω =>
    unfold Input at h
    rw [hd] at h
    cases h with
    | intro n hn => rw [hn]; exact T.fund_ofNat_isNF s.1 s.2 n
  | Ω l => exact T.fund_omega_isNF s.1 l t.1 s.2 hd t.2 (input_bound h l hd)

theorem stage_intro {X : T.NF → Prop} {s : T.NF}
    (h : ∀ (t : T.NF) (ht : Input X s t),
      Stage X ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩) : Stage X s := by
  apply reduction.stage_intro
  intro b hb
  cases hb with
  | intro t ht =>
    have heq : b = ⟨T.fund s.1 t.1, fund_isNF_of_input ht.1⟩ := Subtype.ext ht.2
    rw [heq]
    exact h t ht.1

theorem stage_fund {X : T.NF → Prop} {s t : T.NF}
    (hs : Stage X s) (ht : Input X s t) :
    Stage X ⟨T.fund s.1 t.1, fund_isNF_of_input ht⟩ :=
  reduction.stage_inv hs ⟨t, ht, rfl⟩

theorem stage_zero (X : T.NF → Prop) : Stage X ⟨Z, T.isNF.z⟩ := by
  apply stage_intro
  intro t ht
  exact False.elim ht

theorem stage_add_one {X : T.NF → Prop} {s : T.NF} (hs : Stage X s) :
    Stage X ⟨s.1 + P Z Z Z, T.add_one_isNF s.1 s.2⟩ := by
  apply stage_intro
  intro t ht
  have heq : (⟨T.fund (s.1 + P Z Z Z) t.1, fund_isNF_of_input ht⟩ : T.NF) = s :=
    Subtype.ext (T.fund_add_one s.1 t.1)
  rw [heq]
  exact hs

theorem ofNat_add_one (n : Nat) : T.ofNat n + P Z Z Z = T.ofNat (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P Z Z (T.ofNat n + P Z Z Z) = P Z Z (T.ofNat (n + 1))
    exact congrArg (P Z Z) ih

theorem stage_ofNat (X : T.NF → Prop) (n : Nat) :
    Stage X ⟨T.ofNat n, T.ofNat_isNF n⟩ := by
  induction n with
  | zero => exact stage_zero X
  | succ n ih =>
    have h := stage_add_one ih
    have heq : (⟨T.ofNat n + P Z Z Z, T.add_one_isNF _ (T.ofNat_isNF n)⟩ : T.NF) =
        ⟨T.ofNat (n + 1), T.ofNat_isNF (n + 1)⟩ := Subtype.ext (ofNat_add_one n)
    rw [heq] at h
    exact h

theorem dom_index (a : T) : T.dom (P a Z Z) =
    match T.dom a with
    | .Zero => .One
    | .One => .Ω a
    | .ω => .ω
    | .Ω l => .Ω l := rfl

theorem fund_index (a t : T) : T.fund (P a Z Z) t =
    match T.dom a with
    | .Zero => Z
    | .One => t
    | .ω => P (T.fund a t) Z Z
    | .Ω _ => P (T.fund a t) Z Z := by
  rw [T.fund, ite_eq_left rfl]
  rw [show T.dom Z = .Zero from rfl]
  cases hd : T.dom a with
  | Zero => rfl
  | One => rfl
  | ω => rfl
  | Ω l => rfl

/-- Exponent/index formation preserves a relative stage whenever its parameters
already belong to that stage. -/
theorem stage_index {X : T.NF → Prop} (hX : ∀ s, X s → Stage X s)
    {a : T.NF} (ha : Stage X a) : Stage X ⟨P a.1 Z Z, T.isNF_index a.1 a.2⟩ := by
  induction ha with
  | intro a hacc ih =>
    let ia : T.NF := ⟨P a.1 Z Z, T.isNF_index a.1 a.2⟩
    have liftLimit (hd : T.dom ia.1 = T.dom a.1)
        (hf : ∀ t, T.fund ia.1 t = P (T.fund a.1 t) Z Z) : Stage X ia := by
      apply stage_intro
      intro t ht
      have htA : Input X a t := by
        unfold Input at ht ⊢
        rw [hd] at ht
        exact ht
      have ihAt := ih ⟨T.fund a.1 t.1, fund_isNF_of_input htA⟩ ⟨t, htA, rfl⟩
      have heq : (⟨T.fund ia.1 t.1, fund_isNF_of_input ht⟩ : T.NF) =
          ⟨P (T.fund a.1 t.1) Z Z, T.isNF_index _ (fund_isNF_of_input htA)⟩ :=
        Subtype.ext (hf t.1)
      rw [heq]
      exact ihAt
    cases hd : T.dom a.1 with
    | Zero =>
      have haz := T.dom_eq_zero a.1 hd
      have heq : ia = ⟨T.ofNat 1, T.ofNat_isNF 1⟩ := by
        apply Subtype.ext
        change P a.1 Z Z = P Z Z Z
        rw [haz]
      change Stage X ia
      rw [heq]
      exact stage_ofNat X 1
    | One =>
      have hdI : T.dom ia.1 = .Ω a.1 := by
        change T.dom (P a.1 Z Z) = .Ω a.1
        rw [dom_index, hd]
      have hzero : Input X a ⟨Z, T.isNF.z⟩ := by
        unfold Input
        rw [hd]
      have hp := ih ⟨T.fund a.1 Z, fund_isNF_of_input hzero⟩ ⟨⟨Z, T.isNF.z⟩, hzero, rfl⟩
      change Stage X ia
      apply stage_intro
      intro t ht
      have ht' := ht
      unfold Input at ht'
      rw [hdI] at ht'
      have hf : T.fund ia.1 t.1 = t.1 := by
        change T.fund (P a.1 Z Z) t.1 = t.1
        rw [fund_index, hd]
      have heq : (⟨T.fund ia.1 t.1, fund_isNF_of_input ht⟩ : T.NF) = t := Subtype.ext hf
      rw [heq]
      cases ht'.2 with
      | inl htX => exact hX t htX
      | inr htEq =>
        have htPred : t = ⟨P (T.fund a.1 Z) Z Z,
            T.isNF_index _ (fund_isNF_of_input hzero)⟩ := Subtype.ext htEq
        rw [htPred]
        exact hp
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

theorem stage_LF {X : T.NF → Prop} (hX : ∀ s, X s → Stage X s) (n : Nat) :
    Stage X ⟨T.LF n, T.LF_isNF n⟩ := by
  induction n with
  | zero => exact stage_zero X
  | succ n ih => exact stage_index hX ih

theorem relative_cofinal_nonomega (X : T.NF → Prop) (s r : T.NF)
    (hd : ∀ l, T.dom s.1 ≠ .Ω l) (hrs : r.1 < s.1) :
    ∃ c : T.NF, Step (Stage X) c s ∧ r.1 ≤ c.1 := by
  cases hdS : T.dom s.1 with
  | Zero =>
    have hs := T.dom_eq_zero s.1 hdS
    rw [hs] at hrs
    exact False.elim (lt_Z_inv r.1 hrs)
  | One =>
    let c : T.NF := ⟨T.fund s.1 Z, T.fund_one_isNF s.1 s.2 hdS Z⟩
    refine ⟨c, ?_, (T.fund_one_properties s.1 hdS).2.2.1 r.1 hrs⟩
    refine ⟨⟨Z, T.isNF.z⟩, ?_, rfl⟩
    unfold Input
    rw [hdS]
  | ω =>
    cases T.fund_nonomega_cofinal s.1 s.2 hd r.1 r.2 hrs with
    | intro n hn =>
      let c : T.NF := ⟨T.fund s.1 (T.ofNat n), T.fund_ofNat_isNF s.1 s.2 n⟩
      refine ⟨c, ?_, hn⟩
      refine ⟨⟨T.ofNat n, T.ofNat_isNF n⟩, ?_, rfl⟩
      unfold Input
      rw [hdS]
      exact ⟨n, rfl⟩
  | Ω l => exact False.elim (hd l hdS)

theorem input_nonomega {X Y : T.NF → Prop} {s t : T.NF}
    (hd : ∀ l, T.dom s.1 ≠ .Ω l) : Input X s t ↔ Input Y s t := by
  unfold Input
  cases hs : T.dom s.1 with
  | Zero => exact Iff.rfl
  | One => exact Iff.rfl
  | ω => exact Iff.rfl
  | Ω l => exact False.elim (hd l hs)

theorem step_nonomega {X Y : T.NF → Prop} {s r : T.NF}
    (hd : ∀ l, T.dom s.1 ≠ .Ω l) : Step X r s ↔ Step Y r s := by
  apply Iff.intro
  · intro h
    cases h with
    | intro t ht => exact ⟨t, (input_nonomega hd).mp ht.1, ht.2⟩
  · intro h
    cases h with
    | intro t ht => exact ⟨t, (input_nonomega hd).mpr ht.1, ht.2⟩

/-- Below the first uncountable marker, a sequence-reduction proof already
gives accessibility for the full normal-form order. -/
theorem acc_of_stage_below_omega_one {X : T.NF → Prop} {s : T.NF}
    (hs : Stage X s) :
    s.1 < P (P Z Z Z) Z Z → Acc (fun a b : T.NF => a.1 < b.1) s := by
  induction hs with
  | intro s hstep ih =>
    intro hbound
    apply Acc.intro
    intro r hrs
    have hd := T.dom_ne_omega_below_omega_one s.1 s.2 hbound
    cases relative_cofinal_nonomega X s r hd hrs with
    | intro c hc =>
      have hcs : Step X c s := (step_nonomega hd).mp hc.1
      have hcBound := T.lt_trans c.1 s.1 _ (reduction.step_lt hcs) hbound
      have hacc := ih c hcs hcBound
      cases hc.2 with
      | inl hrc => exact hacc.inv hrc
      | inr heq =>
        have hrc : r = c := Subtype.ext heq
        rw [hrc]
        exact hacc

end T.Constructive
