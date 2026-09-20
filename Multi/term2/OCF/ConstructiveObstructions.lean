/-
An obstruction to reusing the classical ordinal interface constructively.
This does not rule out constructive well-foundedness proofs for term2.
-/

namespace OCF.ConstructiveObstructions

universe u

/-- Unrestricted minimal-element existence already implies excluded middle
as soon as the relation has a pair of related elements. -/
theorem excluded_middle_of_minimal_elements
    {A : Type u} (r : A → A → Prop) (zero one : A) (hzero : r zero one)
    (hmin : ∀ S : A → Prop, (∃ x, S x) →
      ∃ x, S x ∧ ∀ y, r y x → ¬ S y) :
    ∀ P : Prop, P ∨ ¬ P := by
  intro P
  let S : A → Prop := fun x => (x = zero ∧ P) ∨ x = one
  have inhabited : ∃ x, S x := ⟨one, Or.inr rfl⟩
  cases hmin S inhabited with
  | intro x hx =>
    cases hx.1 with
    | inl hP => exact Or.inl hP.2
    | inr hone =>
      apply Or.inr
      intro hP
      have hzx : r zero x := by
        rw [hone]
        exact hzero
      exact hx.2 zero hzx (Or.inl ⟨rfl, hP⟩)

end OCF.ConstructiveObstructions
