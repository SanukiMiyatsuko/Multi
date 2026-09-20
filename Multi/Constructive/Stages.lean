/-
Constructive infrastructure for well-foundedness proofs using relative
fundamental-sequence reductions. No ordinal comparison or choice is used.
-/

namespace Constructive

universe u

structure Reduction (A : Type u) where
  lt : A → A → Prop
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  step : (A → Prop) → A → A → Prop
  step_lt : ∀ {X a b}, step X b a → lt b a
  step_local : ∀ {X Y a b},
    (∀ z, lt z a → (X z ↔ Y z)) → (step X b a ↔ step Y b a)

namespace Reduction

variable {A : Type u} (R : Reduction A)

def Le (a b : A) : Prop := R.lt a b ∨ a = b

def Stage (X : A → Prop) (a : A) : Prop := Acc (R.step X) a

def Distinguished (X : A → Prop) : Prop :=
  ∀ a, X a → ∀ b, R.Le b a → (X b ↔ R.Stage X b)

/-- Relative cofinality is a separate, concrete obligation on the sequence system. -/
def Cofinal : Prop := ∀ (X : A → Prop) a b,
  R.Stage X a → R.Stage X b → R.lt b a →
  ∃ c, R.step (R.Stage X) c a ∧ R.Le b c

theorem le_refl (a : A) : R.Le a a := Or.inr rfl

theorem lt_of_lt_of_le {a b c : A} (hab : R.lt a b) (hbc : R.Le b c) : R.lt a c := by
  cases hbc with
  | inl hbc => exact R.trans hab hbc
  | inr heq => cases heq; exact hab

theorem lt_of_le_of_lt {a b c : A} (hab : R.Le a b) (hbc : R.lt b c) : R.lt a c := by
  cases hab with
  | inl hab => exact R.trans hab hbc
  | inr heq => cases heq; exact hbc

theorem le_trans {a b c : A} (hab : R.Le a b) (hbc : R.Le b c) : R.Le a c := by
  cases hbc with
  | inl hbc => exact Or.inl (R.lt_of_le_of_lt hab hbc)
  | inr heq => cases heq; exact hab

theorem stage_intro {X : A → Prop} {a : A}
    (h : ∀ b, R.step X b a → R.Stage X b) : R.Stage X a := Acc.intro a h

theorem stage_inv {X : A → Prop} {a b : A}
    (h : R.Stage X a) (hba : R.step X b a) : R.Stage X b := h.inv hba

theorem stage_transport {X Y : A → Prop} {a : A} (h : R.Stage X a) :
    (∀ z, R.lt z a → (X z ↔ Y z)) → R.Stage Y a := by
  induction h with
  | intro a ha ih =>
    intro heq
    apply R.stage_intro
    intro b hb
    have hbX := (R.step_local heq).mpr hb
    have hba := R.step_lt hbX
    apply ih b hbX
    intro z hz
    exact heq z (R.trans hz hba)

theorem stage_local {X Y : A → Prop} {a : A}
    (h : ∀ z, R.lt z a → (X z ↔ Y z)) : R.Stage X a ↔ R.Stage Y a := by
  apply Iff.intro
  · intro ha
    exact R.stage_transport ha h
  · intro ha
    exact R.stage_transport ha (fun z hz => (h z hz).symm)

theorem Distinguished.stage {X : A → Prop} (hX : R.Distinguished X) {a : A}
    (ha : X a) : R.Stage X a := (hX a ha a (R.le_refl a)).mp ha

theorem Distinguished.acc (hcof : R.Cofinal) {X : A → Prop}
    (hX : R.Distinguished X) {a : A} (ha : X a) :
    Acc (fun b a => X b ∧ R.lt b a) a := by
  have hstage := hX.stage R ha
  revert ha
  induction hstage with
  | intro a hs ih =>
    intro ha
    apply Acc.intro
    intro b hb
    have hba : R.Le b a := Or.inl hb.2
    have hbStage := (hX a ha b hba).mp hb.1
    cases hcof X a b (Acc.intro a hs) hbStage hb.2 with
    | intro c hc =>
      have hca := R.step_lt hc.1
      have hstep : R.step X c a :=
        (R.step_local (fun z hz => hX a ha z (Or.inl hz))).mpr hc.1
      have hcStage : R.Stage X c := hs c hstep
      have hcX := (hX a ha c (Or.inl hca)).mpr hcStage
      have hacc := ih c hstep hcX
      cases hc.2 with
      | inl hbc => exact hacc.inv ⟨hb.1, hbc⟩
      | inr heq => cases heq; exact hacc

theorem Distinguished.wellFounded (hcof : R.Cofinal) {X : A → Prop}
    (hX : R.Distinguished X) :
    WellFounded (fun a b : {a // X a} => R.lt a.1 b.1) := by
  constructor
  intro a
  have ha := hX.acc R hcof a.2
  have transfer : ∀ x, Acc (fun b a => X b ∧ R.lt b a) x →
      ∀ hx : X x, Acc (fun a b : {a // X a} => R.lt a.1 b.1) ⟨x, hx⟩ := by
    intro x hx
    induction hx with
    | intro x hs ih =>
      intro hx
      apply Acc.intro
      intro b hb
      exact ih b.1 ⟨b.2, hb⟩ b.2
  exact transfer a.1 ha a.2

def Prefix (X : A → Prop) (a : A) (b : A) : Prop := X b ∧ R.Le b a

theorem stage_prefix {X : A → Prop} {a b : A} (hba : R.Le b a) :
    R.Stage (R.Prefix X a) b ↔ R.Stage X b := by
  apply R.stage_local
  intro z hz
  apply Iff.intro
  · intro h
    exact h.1
  · intro h
    exact ⟨h, Or.inl (R.lt_of_lt_of_le hz hba)⟩

theorem Distinguished.prefix {X : A → Prop} (hX : R.Distinguished X) (a : A) :
    R.Distinguished (R.Prefix X a) := by
  intro b hb c hcb
  have hca := R.le_trans hcb hb.2
  apply Iff.intro
  · intro hc
    exact (R.stage_prefix hca).mpr ((hX b hb.1 c hcb).mp hc.1)
  · intro hc
    exact ⟨(hX b hb.1 c hcb).mpr ((R.stage_prefix hca).mp hc), hca⟩

/-- A compatible new endpoint extends a distinguished initial segment. -/
theorem distinguished_extension {X : A → Prop} {a : A}
    (hbelow : ∀ b, R.lt b a → (X b ↔ R.Stage X b)) :
    R.Distinguished (R.Prefix (R.Stage X) a) := by
  intro b hb c hcb
  have hca := R.le_trans hcb hb.2
  have localEq : ∀ z, R.lt z c → (R.Prefix (R.Stage X) a z ↔ X z) := by
    intro z hz
    have hza := R.lt_of_lt_of_le hz hca
    apply Iff.intro
    · intro hzX
      exact (hbelow z hza).mpr hzX.1
    · intro hzX
      exact ⟨(hbelow z hza).mp hzX, Or.inl hza⟩
  apply Iff.intro
  · intro hc
    exact (R.stage_local localEq).mpr hc.1
  · intro hc
    exact ⟨(R.stage_local localEq).mp hc, hca⟩

theorem acc_union_left {X Y : A → Prop}
    (hY : ∀ a, Y a → Acc (fun b a => Y b ∧ R.lt b a) a)
    {a : A} (ha : Acc (fun b a => X b ∧ R.lt b a) a) :
    Acc (fun b a => (X b ∨ Y b) ∧ R.lt b a) a := by
  induction ha with
  | intro a hX ihX =>
    have withinY : ∀ b, Acc (fun c b => Y c ∧ R.lt c b) b → R.lt b a →
        Acc (fun c b => (X c ∨ Y c) ∧ R.lt c b) b := by
      intro b hb
      induction hb with
      | intro b hB ihB =>
        intro hba
        apply Acc.intro
        intro c hc
        cases hc.1 with
        | inl hcX => exact ihX c ⟨hcX, R.trans hc.2 hba⟩
        | inr hcY => exact ihB c ⟨hcY, hc.2⟩ (R.trans hc.2 hba)
    apply Acc.intro
    intro b hb
    cases hb.1 with
    | inl hbX => exact ihX b ⟨hbX, hb.2⟩
    | inr hbY => exact withinY b (hY b hbY) hb.2

theorem distinguished_union_acc (hcof : R.Cofinal) {X Y : A → Prop}
    (hX : R.Distinguished X) (hY : R.Distinguished Y) (a : A) :
    Acc (fun b a => (X b ∨ Y b) ∧ R.lt b a) a := by
  apply R.acc_union_left (fun b hb => hY.acc R hcof hb)
  apply Acc.intro
  intro b hb
  exact hX.acc R hcof hb.1

theorem distinguished_agree (hcof : R.Cofinal) {X Y : A → Prop}
    (hX : R.Distinguished X) (hY : R.Distinguished Y)
    (a b : A) (ha : X a) (hb : Y b) (c : A) (hca : R.Le c a) (hcb : R.Le c b) :
    X c ↔ Y c := by
  have hc := R.distinguished_union_acc hcof hX hY c
  revert hca hcb
  induction hc with
  | intro c hc ih =>
    intro hca hcb
    have hlocal : ∀ z, R.lt z c → (X z ↔ Y z) := by
      intro z hz
      have hza : R.Le z a := Or.inl (R.lt_of_lt_of_le hz hca)
      have hzb : R.Le z b := Or.inl (R.lt_of_lt_of_le hz hcb)
      apply Iff.intro
      · intro hzX
        exact (ih z ⟨Or.inl hzX, hz⟩ hza hzb).mp hzX
      · intro hzY
        exact (ih z ⟨Or.inr hzY, hz⟩ hza hzb).mpr hzY
    exact Iff.trans (hX a ha c hca)
      (Iff.trans (R.stage_local hlocal) (hY b hb c hcb).symm)

def Universal (a : A) : Prop := ∃ X : A → Prop, R.Distinguished X ∧ X a

theorem Distinguished.universal {X : A → Prop} (hX : R.Distinguished X)
    {a : A} (ha : X a) : R.Universal a := ⟨X, hX, ha⟩

theorem Distinguished.initial_universal (hcof : R.Cofinal) {X : A → Prop}
    (hX : R.Distinguished X) {a b : A} (ha : X a) (hb : R.Universal b)
    (hba : R.Le b a) : X b := by
  cases hb with
  | intro Y hY =>
    exact (R.distinguished_agree hcof hX hY.1 a b ha hY.2 b hba (R.le_refl b)).mpr hY.2

theorem universal_distinguished (hcof : R.Cofinal) : R.Distinguished R.Universal := by
  intro a ha b hba
  cases ha with
  | intro X hX =>
    have hlocal : ∀ z, R.lt z b → (R.Universal z ↔ X z) := by
      intro z hz
      apply Iff.intro
      · intro hzU
        exact hX.1.initial_universal R hcof hX.2 hzU
          (Or.inl (R.lt_of_lt_of_le hz hba))
      · intro hzX
        exact hX.1.universal R hzX
    apply Iff.intro
    · intro hb
      have hbX := hX.1.initial_universal R hcof hX.2 hb hba
      exact (R.stage_local hlocal).mpr ((hX.1 a hX.2 b hba).mp hbX)
    · intro hb
      exact hX.1.universal R ((hX.1 a hX.2 b hba).mpr ((R.stage_local hlocal).mp hb))

theorem universal_acc (hcof : R.Cofinal) {a : A} (ha : R.Universal a) :
    Acc (fun b a => R.Universal b ∧ R.lt b a) a :=
  (R.universal_distinguished hcof).acc R hcof ha

theorem universal_wellFounded (hcof : R.Cofinal) :
    WellFounded (fun a b : {a // R.Universal a} => R.lt a.1 b.1) :=
  (R.universal_distinguished hcof).wellFounded R hcof

theorem universal_extension {a : A}
    (hbelow : ∀ b, R.lt b a → (R.Universal b ↔ R.Stage R.Universal b))
    (ha : R.Stage R.Universal a) : R.Universal a := by
  refine ⟨R.Prefix (R.Stage R.Universal) a, R.distinguished_extension hbelow, ?_⟩
  exact ⟨ha, R.le_refl a⟩

theorem universal_of_closed (hcof : R.Cofinal) {a : A}
    (hchildren : ∀ b, R.step R.Universal b a → R.Universal b)
    (hconvert : ∀ b, R.step (R.Stage R.Universal) b a → R.step R.Universal b a) :
    R.Universal a := by
  have hU := R.universal_distinguished hcof
  have ha : R.Stage R.Universal a :=
    R.stage_intro (fun b hb => hU.stage R (hchildren b hb))
  apply R.universal_extension
  · intro b hba
    apply Iff.intro
    · intro hb
      exact hU.stage R hb
    · intro hb
      cases hcof R.Universal a b ha hb hba with
      | intro c hc =>
        have hcU := hchildren c (hconvert c hc.1)
        exact (hU c hcU b hc.2).mpr hb
  · exact ha

theorem wellFounded_of_universal (hcof : R.Cofinal) (hall : ∀ a, R.Universal a) :
    WellFounded R.lt := by
  have hU := R.universal_wellFounded hcof
  exact InvImage.wf (fun a => (⟨a, hall a⟩ : {a // R.Universal a})) hU

end Reduction
end Constructive
