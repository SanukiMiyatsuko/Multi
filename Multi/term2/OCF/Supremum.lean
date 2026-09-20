import Multi.term2.OCF.Range

namespace OCF.Ordinal

universe u

def SupPoint {I : Type u} (f : I → Ordinal.{u}) :=
  (i : I) × (representative (f i)).Carrier

noncomputable def supPointValue {I : Type u} (f : I → Ordinal.{u}) (p : SupPoint f) :
    Ordinal.{u} := type ((representative (f p.1)).below p.2)

def supSetoid {I : Type u} (f : I → Ordinal.{u}) : Setoid (SupPoint f) where
  r p q := supPointValue f p = supPointValue f q
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h k => h.trans k
  }

def SupCarrier {I : Type u} (f : I → Ordinal.{u}) := Quotient (supSetoid f)

noncomputable def supValue {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f) :
    Ordinal.{u} := Quotient.liftOn x (supPointValue f) (fun _ _ h => h)

theorem supValue_injective {I : Type u} (f : I → Ordinal.{u}) (x y : SupCarrier f) :
    supValue f x = supValue f y → x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact Quotient.sound h

theorem supValue_downward {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f)
    (a : Ordinal.{u}) : a < supValue f x → ∃ y, supValue f y = a := by
  refine Quotient.inductionOn x ?_
  intro p h
  have ha : a < f p.1 := lt_trans a _ (f p.1) h (initial_lt (f p.1) p.2)
  cases initial_surjective (f p.1) a ha with
  | intro b hb =>
    exact Exists.intro (Quotient.mk (supSetoid f) ⟨p.1, b⟩) hb.symm

/-- The least upper bound of any small family of small ordinals. -/
noncomputable def sup {I : Type u} (f : I → Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (supValue f) (supValue_injective f))

theorem lt_sup_iff {I : Type u} (f : I → Ordinal.{u}) (a : Ordinal.{u}) :
    a < sup f ↔ ∃ i, a < f i := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (supValue f) (supValue_injective f)
        (supValue_downward f) a).mp h with
    | intro x hx =>
      revert hx
      refine Quotient.inductionOn x ?_
      intro p hp
      rw [hp]
      exact Exists.intro p.1 (initial_lt (f p.1) p.2)
  · intro h
    cases h with
    | intro i hi =>
      cases initial_surjective (f i) a hi with
      | intro b hb =>
        apply (lt_type_orderOn_iff (supValue f) (supValue_injective f)
          (supValue_downward f) a).mpr
        exact Exists.intro (Quotient.mk (supSetoid f) ⟨i, b⟩) hb

theorem le_sup {I : Type u} (f : I → Ordinal.{u}) (i : I) : f i ≤ sup f := by
  apply (not_lt_iff_le (sup f) (f i)).mp
  intro h
  exact lt_irrefl (sup f) ((lt_sup_iff f (sup f)).mpr (Exists.intro i h))

theorem sup_le_iff {I : Type u} (f : I → Ordinal.{u}) (b : Ordinal.{u}) :
    sup f ≤ b ↔ ∀ i, f i ≤ b := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_sup f i) h
  · intro h
    apply (not_lt_iff_le b (sup f)).mp
    intro hb
    cases (lt_sup_iff f b).mp hb with
    | intro i hi => exact ((not_lt_iff_le b (f i)).mpr (h i)) hi

theorem sup_mono {I : Type u} (f g : I → Ordinal.{u}) (h : ∀ i, f i ≤ g i) :
    sup f ≤ sup g := by
  apply (sup_le_iff f (sup g)).mpr
  intro i
  exact le_trans (h i) (le_sup g i)

noncomputable def zero : Ordinal.{u} := sup (fun x : PEmpty.{u+1} => nomatch x)

noncomputable instance : OfNat Ordinal.{u} 0 where
  ofNat := zero

theorem not_lt_zero (a : Ordinal.{u}) : ¬ a < 0 := by
  intro h
  cases (lt_sup_iff (fun x : PEmpty.{u+1} => nomatch x) a).mp h with
  | intro x _ => exact PEmpty.elim x

theorem zero_le (a : Ordinal.{u}) : 0 ≤ a :=
  (not_lt_iff_le a 0).mp (not_lt_zero a)

theorem zero_lt_iff_ne_zero (a : Ordinal.{u}) : 0 < a ↔ a ≠ 0 := by
  apply Iff.intro
  · intro h heq
    cases heq
    exact lt_irrefl 0 h
  · intro h
    cases zero_le a with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (h heq.symm)

noncomputable def succValue (a : Ordinal.{u}) : Option (representative a).Carrier → Ordinal.{u}
  | none => a
  | some x => type ((representative a).below x)

theorem succValue_injective (a : Ordinal.{u}) (x y : Option (representative a).Carrier) :
    succValue a x = succValue a y → x = y := by
  cases x with
  | none =>
    cases y with
    | none => intro _; rfl
    | some y =>
      intro h
      have hy := initial_lt a y
      change a = type ((representative a).below y) at h
      rw [← h] at hy
      exact False.elim (lt_irrefl a hy)
  | some x =>
    cases y with
    | none =>
      intro h
      have hx := initial_lt a x
      change type ((representative a).below x) = a at h
      rw [h] at hx
      exact False.elim (lt_irrefl a hx)
    | some y =>
      intro h
      exact congrArg Option.some (initial_injective a x y h)

theorem succValue_downward (a : Ordinal.{u}) (x : Option (representative a).Carrier)
    (b : Ordinal.{u}) (h : b < succValue a x) : ∃ y, succValue a y = b := by
  have hba : b < a := by
    cases x with
    | none => exact h
    | some x => exact lt_trans b _ a h (initial_lt a x)
  cases initial_surjective a b hba with
  | intro y hy => exact Exists.intro (some y) hy.symm

noncomputable def succ (a : Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (succValue a) (succValue_injective a))

theorem lt_succ_iff_le (a b : Ordinal.{u}) : a < succ b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (succValue b) (succValue_injective b)
        (succValue_downward b) a).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inr hx
      | some x =>
        rw [hx]
        exact Or.inl (initial_lt b x)
  · intro h
    apply (lt_type_orderOn_iff (succValue b) (succValue_injective b)
      (succValue_downward b) a).mpr
    cases h with
    | inl h =>
      cases initial_surjective b a h with
      | intro x hx => exact Exists.intro (some x) hx
    | inr h => exact Exists.intro none h

theorem lt_succ_self (a : Ordinal.{u}) : a < succ a :=
  (lt_succ_iff_le a a).mpr (le_refl a)

theorem lt_of_le_of_lt {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b < c) : a < c := by
  cases hab with
  | inl hab => exact lt_trans a b c hab hbc
  | inr hab =>
    cases hab
    exact hbc

theorem lt_of_lt_of_le {a b c : Ordinal.{u}} (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hbc => exact lt_trans a b c hab hbc
  | inr hbc =>
    cases hbc
    exact hab

theorem succ_le_iff_lt (a b : Ordinal.{u}) : succ a ≤ b ↔ a < b := by
  apply Iff.intro
  · intro h
    exact lt_of_lt_of_le (lt_succ_self a) h
  · intro h
    apply (not_lt_iff_le b (succ a)).mp
    intro hb
    have hba := (lt_succ_iff_le b a).mp hb
    exact lt_irrefl b (lt_of_le_of_lt hba h)

theorem succ_mono {a b : Ordinal.{u}} (h : a ≤ b) : succ a ≤ succ b :=
  (succ_le_iff_lt a (succ b)).mpr ((lt_succ_iff_le a b).mpr h)

end OCF.Ordinal
