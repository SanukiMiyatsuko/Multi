import Multi.term2.OCF.Supremum

namespace OCF.Ordinal

universe u

theorem eq_of_lt_iff (a b : Ordinal.{u}) (h : ∀ c, c < a ↔ c < b) : a = b := by
  cases lt_total a b with
  | inl hab => exact False.elim (lt_irrefl a ((h a).mpr hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba => exact False.elim (lt_irrefl b ((h b).mp hba))

noncomputable def add (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun b ih => sup (fun x : Option (representative b).Carrier =>
    match x with
    | none => a
    | some x => succ (ih (type ((representative b).below x)) (initial_lt b x))))

noncomputable instance : Add Ordinal.{u} where
  add := add

theorem add_eq (a b : Ordinal.{u}) :
    a + b = sup (fun x : Option (representative b).Carrier =>
      match x with
      | none => a
      | some x => succ (a + type ((representative b).below x))) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem lt_add_iff (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c ≤ a + d := by
  rw [add_eq a b]
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ c).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inl hx
      | some x =>
        exact Or.inr (Exists.intro (type ((representative b).below x))
          (And.intro (initial_lt b x) ((lt_succ_iff_le c _).mp hx)))
  · intro h
    apply (lt_sup_iff _ c).mpr
    cases h with
    | inl h => exact Exists.intro none h
    | inr h =>
      cases h with
      | intro d hd =>
        cases initial_surjective b d hd.1 with
        | intro x hx =>
          refine Exists.intro (some x) ?_
          apply (lt_succ_iff_le c _).mpr
          rw [← hx]
          exact hd.2

theorem le_add (a b : Ordinal.{u}) : a ≤ a + b := by
  rw [add_eq a b]
  exact le_sup _ none

theorem add_lt_add_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b < c) :
    a + b < a + c :=
  (lt_add_iff a c (a + b)).mpr (Or.inr (Exists.intro b (And.intro h (le_refl _))))

theorem add_mono_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b ≤ c) :
    a + b ≤ a + c := by
  cases h with
  | inl h => exact Or.inl (add_lt_add_right a h)
  | inr h =>
    cases h
    exact le_refl _

theorem add_zero (a : Ordinal.{u}) : a + 0 = a := by
  apply le_antisymm
  · rw [add_eq a 0]
    apply (sup_le_iff _ a).mpr
    intro x
    cases x with
    | none => exact le_refl a
    | some x => exact False.elim (not_lt_zero _ (initial_lt 0 x))
  · exact le_add a 0

theorem zero_add (b : Ordinal.{u}) : 0 + b = b := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    apply eq_of_lt_iff
    intro c
    apply Iff.intro
    · intro hcb
      cases (lt_add_iff 0 b c).mp hcb with
      | inl hc0 => exact False.elim (not_lt_zero c hc0)
      | inr hcd =>
        cases hcd with
        | intro d hd =>
          have hcd := hd.2
          rw [ih d hd.1] at hcd
          exact lt_of_le_of_lt hcd hd.1
    · intro hcb
      apply (lt_add_iff 0 b c).mpr
      apply Or.inr
      refine Exists.intro c (And.intro hcb ?_)
      rw [ih c hcb]
      exact le_refl c

theorem add_succ (a b : Ordinal.{u}) : a + succ b = succ (a + b) := by
  apply eq_of_lt_iff
  intro c
  apply Iff.intro
  · intro hc
    apply (lt_succ_iff_le c (a + b)).mpr
    cases (lt_add_iff a (succ b) c).mp hc with
    | inl hca => exact Or.inl (lt_of_lt_of_le hca (le_add a b))
    | inr hcd =>
      cases hcd with
      | intro d hd =>
        exact le_trans hd.2 (add_mono_right a ((lt_succ_iff_le d b).mp hd.1))
  · intro hc
    apply (lt_add_iff a (succ b) c).mpr
    exact Or.inr (Exists.intro b
      (And.intro (lt_succ_self b) ((lt_succ_iff_le c (a + b)).mp hc)))

theorem add_mono_left {a b : Ordinal.{u}} (hab : a ≤ b) (c : Ordinal.{u}) :
    a + c ≤ b + c := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    rw [add_eq a c, add_eq b c]
    apply sup_mono
    intro x
    cases x with
    | none => exact hab
    | some x => exact succ_mono (ih _ (initial_lt c x))

theorem right_le_add (a b : Ordinal.{u}) : b ≤ a + b := by
  have h := add_mono_left (zero_le a) b
  rw [zero_add b] at h
  exact h

theorem add_assoc (a b c : Ordinal.{u}) : (a + b) + c = a + (b + c) := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    apply eq_of_lt_iff
    intro x
    apply Iff.intro
    · intro hx
      cases (lt_add_iff (a + b) c x).mp hx with
      | inl hxab => exact lt_of_lt_of_le hxab (add_mono_right a (le_add b c))
      | inr hxd =>
        cases hxd with
        | intro d hd =>
          have hxd := hd.2
          rw [ih d hd.1] at hxd
          exact lt_of_le_of_lt hxd (add_lt_add_right a (add_lt_add_right b hd.1))
    · intro hx
      cases (lt_add_iff a (b + c) x).mp hx with
      | inl hxa => exact lt_of_lt_of_le hxa (le_trans (le_add a b) (le_add (a + b) c))
      | inr hxy =>
        cases hxy with
        | intro y hy =>
          cases (lt_add_iff b c y).mp hy.1 with
          | inl hyb =>
            exact lt_of_le_of_lt hy.2
              (lt_of_lt_of_le (add_lt_add_right a hyb) (le_add (a + b) c))
          | inr hyd =>
            cases hyd with
            | intro d hd =>
              have hxy := le_trans hy.2 (add_mono_right a hd.2)
              rw [← ih d hd.1] at hxy
              exact lt_of_le_of_lt hxy (add_lt_add_right (a + b) hd.1)

theorem add_right_cancel {a b c : Ordinal.{u}} (h : a + b = a + c) : b = c := by
  cases lt_total b c with
  | inl hbc =>
    have hlt := add_lt_add_right a hbc
    rw [h] at hlt
    exact False.elim (lt_irrefl (a + c) hlt)
  | inr hrest =>
    cases hrest with
    | inl hbc => exact hbc
    | inr hcb =>
      have hlt := add_lt_add_right a hcb
      rw [h] at hlt
      exact False.elim (lt_irrefl (a + c) hlt)

theorem lt_add_iff_eq (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c = a + d := by
  apply Iff.intro
  · intro h
    cases (lt_add_iff a b c).mp h with
    | inl hca => exact Or.inl hca
    | inr hd =>
      cases Ordinal.exists_min (fun d => d < b ∧ c ≤ a + d) hd with
      | intro d hdmin =>
        cases hdmin.1.2 with
        | inr hcd => exact Or.inr (Exists.intro d (And.intro hdmin.1.1 hcd))
        | inl hcd =>
          cases (lt_add_iff a d c).mp hcd with
          | inl hca => exact Or.inl hca
          | inr he =>
            cases he with
            | intro e he =>
              exact False.elim
                (hdmin.2 e he.1 (And.intro (lt_trans e d b he.1 hdmin.1.1) he.2))
  · intro h
    apply (lt_add_iff a b c).mpr
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | intro d hd => exact Or.inr (Exists.intro d (And.intro hd.1 (Or.inr hd.2)))

theorem le_add_cases (a b c : Ordinal.{u}) (h : c ≤ a + b) (hca : ¬ c < a) :
    ∃ d, d ≤ b ∧ c = a + d := by
  cases h with
  | inr h => exact Exists.intro b (And.intro (le_refl b) h)
  | inl h =>
    cases (lt_add_iff_eq a b c).mp h with
    | inl h => exact False.elim (hca h)
    | inr h =>
      cases h with
      | intro d hd => exact Exists.intro d (And.intro (Or.inl hd.1) hd.2)

theorem exists_add_of_le (a b : Ordinal.{u}) (h : a ≤ b) : ∃ c, b = a + c := by
  have hb : b < a + succ b := lt_of_lt_of_le (lt_succ_self b) (right_le_add a (succ b))
  cases (lt_add_iff_eq a (succ b) b).mp hb with
  | inl hba => exact False.elim (((not_lt_iff_le b a).mpr h) hba)
  | inr hc =>
    cases hc with
    | intro c hc => exact Exists.intro c hc.2

def AddPrincipal (k : Ordinal.{u}) : Prop :=
  ∀ a b, a < k → b < k → a + b < k

theorem AddPrincipal.absorb {k : Ordinal.{u}} (hk : AddPrincipal k)
    {a : Ordinal.{u}} (ha : a < k) : a + k = k := by
  apply le_antisymm
  · apply (not_lt_iff_le k (a + k)).mp
    intro h
    cases (lt_add_iff a k k).mp h with
    | inl hka => exact lt_asymm ha hka
    | inr hd =>
      cases hd with
      | intro d hd => exact lt_irrefl k (lt_of_le_of_lt hd.2 (hk a d ha hd.1))
  · exact right_le_add a k

theorem AddPrincipal.absorb_of_le {k : Ordinal.{u}} (hk : AddPrincipal k)
    {a b : Ordinal.{u}} (ha : a < k) (hb : k ≤ b) : a + b = b := by
  cases exists_add_of_le k b hb with
  | intro c hc =>
    rw [hc, ← add_assoc, hk.absorb ha]

theorem succ_zero_principal : AddPrincipal (succ (0 : Ordinal.{u})) := by
  intro a b ha hb
  have ea := le_antisymm ((lt_succ_iff_le a 0).mp ha) (zero_le a)
  have eb := le_antisymm ((lt_succ_iff_le b 0).mp hb) (zero_le b)
  rw [ea, eb, add_zero]
  exact lt_succ_self 0

end OCF.Ordinal
