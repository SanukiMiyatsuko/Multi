import Multi.term2.OCF.WellOrder

namespace OCF

universe u

def WellOrder.isoSetoid : Setoid WellOrder.{u} where
  r A B := Nonempty (WellOrder.Iso A B)
  iseqv := {
    refl := fun A => Nonempty.intro (WellOrder.Iso.refl A)
    symm := fun h => by
      cases h with
      | intro e => exact Nonempty.intro e.symm
    trans := fun hAB hBC => by
      cases hAB with
      | intro e =>
        cases hBC with
        | intro f => exact Nonempty.intro (e.trans f)
  }

/-- Small well-orders, identified up to order isomorphism. -/
def Ordinal : Type (u + 1) := Quotient WellOrder.isoSetoid.{u}

namespace Ordinal

def type (A : WellOrder.{u}) : Ordinal.{u} := Quotient.mk WellOrder.isoSetoid A

def lt (a b : Ordinal.{u}) : Prop :=
  Quotient.liftOn₂ a b WellOrder.Below (by
    intro A B C D hAC hBD
    cases hAC with
    | intro e =>
      cases hBD with
      | intro f => exact propext (WellOrder.Below.congr e f))

instance : LT Ordinal.{u} where
  lt := lt

theorem type_lt_type (A B : WellOrder.{u}) :
    type A < type B ↔ WellOrder.Below A B :=
  Iff.intro (fun h => h) (fun h => h)

theorem type_eq_of_iso {A B : WellOrder.{u}} (e : WellOrder.Iso A B) :
    type A = type B := Quotient.sound (Nonempty.intro e)

theorem iso_of_type_eq {A B : WellOrder.{u}} (h : type A = type B) :
    Nonempty (WellOrder.Iso A B) := Quotient.exact h

theorem type_acc (A : WellOrder.{u}) : Acc (fun a b : Ordinal.{u} => a < b) (type A) := by
  have hA := WellOrder.below_wellFounded.apply A
  induction hA with
  | intro A _ ih =>
    apply Acc.intro
    intro b
    refine Quotient.inductionOn b ?_
    intro B hBA
    exact ih B hBA

theorem lt_wellFounded : WellFounded (fun a b : Ordinal.{u} => a < b) := by
  apply WellFounded.intro
  intro a
  refine Quotient.inductionOn a ?_
  intro A
  exact type_acc A

theorem lt_irrefl (a : Ordinal.{u}) : ¬ a < a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact WellOrder.Below.irrefl A

theorem lt_trans (a b c : Ordinal.{u}) : a < b → b < c → a < c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C hAB hBC
  exact WellOrder.Below.trans hAB hBC

theorem lt_asymm {a b : Ordinal.{u}} (hab : a < b) : ¬ b < a := by
  intro hba
  exact lt_irrefl a (lt_trans a b a hab hba)

theorem lt_total (a b : Ordinal.{u}) : a < b ∨ a = b ∨ b < a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  cases WellOrder.compare A B with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro e => exact Or.inr (Or.inl (type_eq_of_iso e))
    | inr h => exact Or.inr (Or.inr h)

instance : LE Ordinal.{u} where
  le a b := a < b ∨ a = b

theorem le_refl (a : Ordinal.{u}) : a ≤ a := Or.inr rfl

theorem le_trans {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab =>
    cases hbc with
    | inl hbc => exact Or.inl (lt_trans a b c hab hbc)
    | inr hbc =>
      cases hbc
      exact Or.inl hab
  | inr hab =>
    cases hab
    exact hbc

theorem le_antisymm {a b : Ordinal.{u}} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | inl hab =>
    cases hba with
    | inl hba => exact False.elim (lt_asymm hab hba)
    | inr hba => exact hba.symm
  | inr hab => exact hab

theorem not_lt_iff_le (a b : Ordinal.{u}) : (¬ a < b) ↔ b ≤ a := by
  apply Iff.intro
  · intro h
    cases lt_total a b with
    | inl hab => exact False.elim (h hab)
    | inr hrest =>
      cases hrest with
      | inl hab => exact Or.inr hab.symm
      | inr hba => exact Or.inl hba
  · intro h hab
    cases h with
    | inl hba => exact lt_asymm hab hba
    | inr hba =>
      cases hba
      exact lt_irrefl a hab

theorem lt_type_iff (a : Ordinal.{u}) (B : WellOrder.{u}) :
    a < type B ↔ ∃ b : B.Carrier, a = type (B.below b) := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Iff.intro
  · intro h
    cases h with
    | intro b hb =>
      cases hb with
      | intro e => exact Exists.intro b (type_eq_of_iso e)
  · intro h
    cases h with
    | intro b hb => exact Exists.intro b (iso_of_type_eq hb)

theorem representative_exists (a : Ordinal.{u}) : ∃ A : WellOrder.{u}, type A = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Exists.intro A rfl

noncomputable def representative (a : Ordinal.{u}) : WellOrder.{u} :=
  Classical.choose (representative_exists a)

theorem type_representative (a : Ordinal.{u}) : type (representative a) = a :=
  Classical.choose_spec (representative_exists a)

theorem initial_lt (a : Ordinal.{u}) (x : (representative a).Carrier) :
    type ((representative a).below x) < a := by
  have h : type ((representative a).below x) < type (representative a) :=
    WellOrder.below_self (representative a) x
  rw [type_representative a] at h
  exact h

theorem initial_injective (a : Ordinal.{u}) (x y : (representative a).Carrier)
    (h : type ((representative a).below x) = type ((representative a).below y)) : x = y := by
  cases iso_of_type_eq h with
  | intro e => exact WellOrder.eq_of_below_iso (representative a) x y e

theorem initial_surjective (a b : Ordinal.{u}) (h : b < a) :
    ∃ x : (representative a).Carrier, b = type ((representative a).below x) := by
  apply (lt_type_iff b (representative a)).mp
  rw [type_representative a]
  exact h

theorem exists_min (P : Ordinal.{u} → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, b < a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, b < c → ¬ P b := by
    intro a
    induction a using lt_wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, b < a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

end Ordinal
end OCF
