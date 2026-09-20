import Multi.term2.OCF.Ordinal

namespace OCF.Ordinal

universe u

theorem initial_lt_iff (a : Ordinal.{u}) (x y : (representative a).Carrier) :
    type ((representative a).below x) < type ((representative a).below y) ↔
      (representative a).lt x y := by
  apply Iff.intro
  · intro h
    exact WellOrder.lt_of_below_below (representative a) x y h
  · intro h
    exact WellOrder.below_below_of_lt (representative a) x y h

/-- A small set of distinct ordinals inherits a well-order. -/
def orderOn {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y) : WellOrder.{u} where
  Carrier := X
  lt x y := f x < f y
  irrefl x := lt_irrefl (f x)
  trans x y z hxy hyz := lt_trans (f x) (f y) (f z) hxy hyz
  total x y := by
    cases lt_total (f x) (f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (hf x y h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf f lt_wellFounded

/-- If the range is downward closed, its elements are their own initial order types. -/
noncomputable def orderOnBelowIso {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    WellOrder.Iso ((orderOn f hf).below x) (representative (f x)) := by
  let F : ((orderOn f hf).below x).Carrier → (representative (f x)).Carrier :=
    fun y => Classical.choose (initial_surjective (f x) (f y.1) y.2)
  have hF : ∀ y, f y.1 = type ((representative (f x)).below (F y)) :=
    fun y => Classical.choose_spec (initial_surjective (f x) (f y.1) y.2)
  let G : (representative (f x)).Carrier → ((orderOn f hf).below x).Carrier :=
    fun b =>
      let y := Classical.choose (hd x _ (initial_lt (f x) b))
      have hy : f y = type ((representative (f x)).below b) :=
        Classical.choose_spec (hd x _ (initial_lt (f x) b))
      ⟨y, by
        change f y < f x
        rw [hy]
        exact initial_lt (f x) b⟩
  have hG : ∀ b, f (G b).1 = type ((representative (f x)).below b) :=
    fun b => Classical.choose_spec (hd x _ (initial_lt (f x) b))
  exact {
    toFun := F
    invFun := G
    left_inv := fun y => Subtype.ext (hf _ _ ((hG (F y)).trans (hF y).symm))
    right_inv := fun b => initial_injective (f x) _ _ ((hF (G b)).symm.trans (hG b))
    lt_iff := fun y z => by
      have h := initial_lt_iff (f x) (F y) (F z)
      rw [← hF y, ← hF z] at h
      exact h.symm
  }

theorem type_orderOn_below {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    type ((orderOn f hf).below x) = f x :=
  (type_eq_of_iso (orderOnBelowIso f hf hd x)).trans (type_representative (f x))

theorem lt_type_orderOn_iff {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (a : Ordinal.{u}) :
    a < type (orderOn f hf) ↔ ∃ x, a = f x := by
  apply Iff.intro
  · intro h
    cases (lt_type_iff a (orderOn f hf)).mp h with
    | intro x hx => exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x))
  · intro h
    cases h with
    | intro x hx =>
      apply (lt_type_iff a (orderOn f hf)).mpr
      exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x).symm)

end OCF.Ordinal
