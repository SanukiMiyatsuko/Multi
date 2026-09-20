import Multi.OCF.Supremum

namespace OCF

universe u

/-- Well-orders on subsets of a fixed small type form a small type. -/
structure SubOrder (X : Type u) where
  domain : X → Prop
  lt : {x : X // domain x} → {x : X // domain x} → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace SubOrder

def toWellOrder {X : Type u} (r : SubOrder X) : WellOrder.{u} where
  Carrier := {x : X // r.domain x}
  lt := r.lt
  irrefl := r.irrefl
  trans := r.trans
  total := r.total
  wellFounded := r.wellFounded

noncomputable def preimage {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) : A :=
  Classical.choose x.2

theorem preimage_spec {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) :
    f (preimage f x) = x.1 := Classical.choose_spec x.2

theorem preimage_image {A X : Type u} (f : A → X)
    (hf : ∀ a b, f a = f b → a = b) (a : A) :
    preimage f ⟨f a, Exists.intro a rfl⟩ = a :=
  hf _ a (preimage_spec f ⟨f a, Exists.intro a rfl⟩)

noncomputable def image {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (_hf : ∀ a b, f a = f b → a = b) : SubOrder X where
  domain x := ∃ a, f a = x
  lt x y := A.lt (preimage f x) (preimage f y)
  irrefl x := A.irrefl (preimage f x)
  trans x y z hxy hyz := A.trans _ _ _ hxy hyz
  total x y := by
    cases A.total (preimage f x) (preimage f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h =>
        apply Or.inr
        apply Or.inl
        apply Subtype.ext
        exact (preimage_spec f x).symm.trans ((congrArg f h).trans (preimage_spec f y))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf (preimage f) A.wellFounded

noncomputable def imageIso {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (hf : ∀ a b, f a = f b → a = b) : WellOrder.Iso A (image A f hf).toWellOrder where
  toFun a := ⟨f a, Exists.intro a rfl⟩
  invFun := preimage f
  left_inv a := preimage_image f hf a
  right_inv x := Subtype.ext (preimage_spec f x)
  lt_iff a b := by
    change A.lt (preimage f ⟨f a, Exists.intro a rfl⟩)
      (preimage f ⟨f b, Exists.intro b rfl⟩) ↔ A.lt a b
    rw [preimage_image f hf a, preimage_image f hf b]

end SubOrder

namespace Ordinal

/-- The least ordinal whose underlying type cannot inject into `X`. -/
noncomputable def hartogs (X : Type u) : Ordinal.{u} :=
  sup (fun r : SubOrder X => succ (type r.toWellOrder))

theorem subOrder_type_lt_hartogs {X : Type u} (r : SubOrder X) :
    type r.toWellOrder < hartogs X :=
  lt_of_lt_of_le (lt_succ_self (type r.toWellOrder))
    (le_sup (fun s : SubOrder X => succ (type s.toWellOrder)) r)

theorem lt_hartogs_of_injective {X : Type u} (a : Ordinal.{u})
    (f : (representative a).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    a < hartogs X := by
  have he := type_eq_of_iso (SubOrder.imageIso (representative a) f hf)
  have h := subOrder_type_lt_hartogs (SubOrder.image (representative a) f hf)
  rw [← he, type_representative a] at h
  exact h

theorem no_injection_hartogs (X : Type u) (f : (representative (hartogs X)).Carrier → X) :
    ¬ (∀ x y, f x = f y → x = y) := by
  intro hf
  exact lt_irrefl (hartogs X) (lt_hartogs_of_injective (hartogs X) f hf)

theorem injection_into_of_le_type (a : Ordinal.{u}) (B : WellOrder.{u})
    (h : a ≤ type B) :
    ∃ f : (representative a).Carrier → B.Carrier, ∀ x y, f x = f y → x = y := by
  cases h with
  | inl h =>
    have h' : type (representative a) < type B := by
      rw [type_representative a]
      exact h
    cases h' with
    | intro b hb =>
      cases hb with
      | intro e =>
        refine Exists.intro (fun x => (e.toFun x).1) ?_
        intro x y hxy
        exact e.injective x y (Subtype.ext hxy)
  | inr h =>
    have h' : type (representative a) = type B := (type_representative a).trans h
    cases iso_of_type_eq h' with
    | intro e => exact Exists.intro e.toFun e.injective

theorem injection_of_le (a b : Ordinal.{u}) (h : a ≤ b) :
    ∃ f : (representative a).Carrier → (representative b).Carrier,
      ∀ x y, f x = f y → x = y := by
  apply injection_into_of_le_type a (representative b)
  rw [type_representative b]
  exact h

theorem injection_of_lt_hartogs {X : Type u} (a : Ordinal.{u}) (h : a < hartogs X) :
    ∃ f : (representative a).Carrier → X, ∀ x y, f x = f y → x = y := by
  cases (lt_sup_iff (fun r : SubOrder X => succ (type r.toWellOrder)) a).mp h with
  | intro r hr =>
    cases injection_into_of_le_type a r.toWellOrder ((lt_succ_iff_le a _).mp hr) with
    | intro f hf =>
      refine Exists.intro (fun x => (f x).1) ?_
      intro x y hxy
      exact hf x y (Subtype.ext hxy)

theorem lt_hartogs_iff_injective {X : Type u} (a : Ordinal.{u}) :
    a < hartogs X ↔
      ∃ f : (representative a).Carrier → X, ∀ x y, f x = f y → x = y := by
  apply Iff.intro
  · exact injection_of_lt_hartogs a
  · intro h
    cases h with
    | intro f hf => exact lt_hartogs_of_injective a f hf

theorem self_lt_hartogs (a : Ordinal.{u}) : a < hartogs (representative a).Carrier :=
  lt_hartogs_of_injective a (fun x => x) (fun _ _ h => h)

theorem hartogs_mono {X Y : Type u} (f : X → Y) (hf : ∀ x y, f x = f y → x = y) :
    hartogs X ≤ hartogs Y := by
  apply (not_lt_iff_le (hartogs Y) (hartogs X)).mp
  intro h
  cases injection_of_lt_hartogs (hartogs Y) h with
  | intro g hg =>
    apply no_injection_hartogs Y (fun x => f (g x))
    intro x y hxy
    exact hg x y (hf (g x) (g y) hxy)

theorem exists_not_range_lt_hartogs {X : Type u} (f : X → Ordinal.{u}) :
    ∃ a, a < hartogs X ∧ ¬ ∃ x, f x = a := by
  classical
  apply Classical.byContradiction
  intro h
  have hit : ∀ a, a < hartogs X → ∃ x, f x = a := by
    intro a ha
    apply Classical.byContradiction
    intro hn
    exact h (Exists.intro a (And.intro ha hn))
  let g : (representative (hartogs X)).Carrier → X :=
    fun y => Classical.choose (hit _ (initial_lt (hartogs X) y))
  have hg : ∀ y, f (g y) = type ((representative (hartogs X)).below y) :=
    fun y => Classical.choose_spec (hit _ (initial_lt (hartogs X) y))
  apply no_injection_hartogs X g
  intro y z hyz
  apply initial_injective (hartogs X)
  exact (hg y).symm.trans ((congrArg f hyz).trans (hg z))

end Ordinal
end OCF
