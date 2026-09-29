import Multi.term3.Denis.Cardinals

/-! Small indexing types for a regular cardinal. These lemmas prove the
size bound for finite closure expressions without assuming it as a field
of the OCF model. -/

namespace OCF.Denis

open Ordinal

noncomputable section

def SmallFor (k : O) (X : Type) : Prop :=
  ∀ f : X → O, (∀ x, f x < k) → ∃ b, b < k ∧ ∀ x, f x < b

theorem regular_pos {k : O} (hk : UncountableRegular k) : 0 < k :=
  lt_trans _ _ _ (finite_lt_omega 0) hk.1

theorem small_representative {k : O} (hk : UncountableRegular k)
    (b : O) (hb : b < k) : SmallFor k (representative b).Carrier := hk.2 b hb

theorem SmallFor.of_injective {k : O} (hk : 0 < k) {X Y : Type}
    (hY : SmallFor k Y) (g : X → Y) (hg : ∀ x y, g x = g y → x = y) : SmallFor k X := by
  classical
  intro f hf
  let F : Y → O := fun y => if h : ∃ x, g x = y then f (Classical.choose h) else 0
  have hF : ∀ y, F y < k := by
    intro y
    dsimp [F]
    split
    · exact hf _
    · exact hk
  obtain ⟨b, hb, hbound⟩ := hY F hF
  refine ⟨b, hb, ?_⟩
  intro x
  have h := hbound (g x)
  dsimp [F] at h
  rw [dite_eq_left (show ∃ y, g y = g x from ⟨x, rfl⟩)] at h
  have heq := hg _ x (Classical.choose_spec (show ∃ y, g y = g x from ⟨x, rfl⟩))
  rw [heq] at h
  exact h

theorem finite_injective {n m : Nat} (h : finite n = finite m) : n = m := by
  cases Nat.lt_trichotomy n m with
  | inl hnm =>
    have hl := (lt_finite_iff (finite n) m).mpr ⟨n, hnm, rfl⟩
    rw [h] at hl
    exact False.elim (lt_irrefl _ hl)
  | inr hrest =>
    cases hrest with
    | inl heq => exact heq
    | inr hmn =>
      have hl := (lt_finite_iff (finite m) n).mpr ⟨m, hmn, rfl⟩
      rw [h] at hl
      exact False.elim (lt_irrefl _ hl)

theorem small_nat {k : O} (hk : UncountableRegular k) : SmallFor k Nat := by
  let g : Nat → (representative omega).Carrier :=
    fun n => Classical.choose (initial_surjective omega (finite n) (finite_lt_omega n))
  have hg : ∀ n, finite n = type ((representative omega).below (g n)) :=
    fun n => Classical.choose_spec (initial_surjective omega (finite n) (finite_lt_omega n))
  apply SmallFor.of_injective (regular_pos hk) (small_representative hk omega hk.1) g
  intro n m h
  apply finite_injective
  rw [hg n, hg m, h]

theorem SmallFor.sum {k : O} {X Y : Type}
    (hX : SmallFor k X) (hY : SmallFor k Y) : SmallFor k (Sum X Y) := by
  intro f hf
  obtain ⟨a, ha, hfa⟩ := hX (fun x => f (.inl x)) (fun x => hf (.inl x))
  obtain ⟨b, hb, hfb⟩ := hY (fun y => f (.inr y)) (fun y => hf (.inr y))
  cases lt_total a b with
  | inl hab =>
    refine ⟨b, hb, ?_⟩
    intro x
    cases x with
    | inl x => exact lt_trans _ _ _ (hfa x) hab
    | inr y => exact hfb y
  | inr hrest =>
    have hba : b ≤ a := by
      cases hrest with
      | inl hab => exact Or.inr hab.symm
      | inr hba => exact Or.inl hba
    refine ⟨a, ha, ?_⟩
    intro x
    cases x with
    | inl x => exact hfa x
    | inr y => exact lt_of_lt_of_le (hfb y) hba

theorem SmallFor.sigma {k : O} {X : Type} {Y : X → Type}
    (hX : SmallFor k X) (hY : ∀ x, SmallFor k (Y x)) : SmallFor k (Sigma Y) := by
  intro f hf
  have h : ∀ x, ∃ b, b < k ∧ ∀ y, f ⟨x, y⟩ < b :=
    fun x => hY x (fun y => f ⟨x, y⟩) (fun y => hf ⟨x, y⟩)
  let bounds : X → O := fun x => Classical.choose (h x)
  have hbounds := fun x => Classical.choose_spec (h x)
  obtain ⟨b, hb, hbound⟩ := hX bounds (fun x => (hbounds x).1)
  exact ⟨b, hb, fun ⟨x, y⟩ => lt_trans _ _ _ ((hbounds x).2 y) (hbound x)⟩

theorem SmallFor.prod {k : O} (hk : 0 < k) {X Y : Type}
    (hX : SmallFor k X) (hY : SmallFor k Y) : SmallFor k (X × Y) := by
  apply SmallFor.of_injective hk (hX.sigma (fun _ => hY)) (fun p => ⟨p.1, p.2⟩)
  intro x y h
  cases x
  cases y
  cases h
  rfl

theorem small_unit {k : O} (hk : UncountableRegular k) : SmallFor k Unit := by
  apply SmallFor.of_injective (regular_pos hk) (small_nat hk) (fun _ => 0)
  intro x y _
  cases x
  cases y
  rfl

theorem small_fin {k : O} (hk : UncountableRegular k) (n : Nat) : SmallFor k (Fin n) :=
  SmallFor.of_injective (regular_pos hk) (small_nat hk) Fin.val
    (fun _ _ h => Fin.ext h)

inductive Expr (X : Type) where
  | zero
  | leaf (x : X)
  | node (op : Fin 3) (left right : Expr X)

def Expr.height {X : Type} : Expr X → Nat
  | .zero => 0
  | .leaf _ => 0
  | .node _ a b => max a.height b.height + 1

def Expr.Bounded (X : Type) (n : Nat) := {c : Expr X // c.height ≤ n}

def Expr.splitZero {X : Type} (c : Expr.Bounded X 0) : Unit ⊕ X :=
  match c with
  | ⟨.zero, _⟩ => .inl ()
  | ⟨.leaf x, _⟩ => .inr x
  | ⟨.node _ _ _, h⟩ => False.elim (Nat.not_succ_le_zero _ h)

theorem Expr.splitZero_injective {X : Type} (a b : Expr.Bounded X 0)
    (h : Expr.splitZero a = Expr.splitZero b) : a = b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b
  all_goals first
    | exact False.elim (Nat.not_succ_le_zero _ ha)
    | exact False.elim (Nat.not_succ_le_zero _ hb)
    | simp_all [Expr.splitZero, Expr.Bounded]

def Expr.splitSucc {X : Type} {n : Nat} (c : Expr.Bounded X (n + 1)) :
    (Unit ⊕ X) ⊕ (Fin 3 × Expr.Bounded X n × Expr.Bounded X n) :=
  match c with
  | ⟨.zero, _⟩ => .inl (.inl ())
  | ⟨.leaf x, _⟩ => .inl (.inr x)
  | ⟨.node op a b, h⟩ => .inr (op,
      ⟨a, Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_succ_le_succ h)⟩,
      ⟨b, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_succ_le_succ h)⟩)

theorem Expr.splitSucc_injective {X : Type} {n : Nat} (a b : Expr.Bounded X (n + 1))
    (h : Expr.splitSucc a = Expr.splitSucc b) : a = b := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  cases a <;> cases b <;>
    simp_all [Expr.splitSucc, Expr.Bounded, Subtype.mk.injEq]

theorem small_expr_bounded {k : O} (hk : UncountableRegular k) {X : Type}
    (hX : SmallFor k X) (n : Nat) : SmallFor k (Expr.Bounded X n) := by
  induction n with
  | zero =>
    exact SmallFor.of_injective (regular_pos hk) ((small_unit hk).sum hX)
      Expr.splitZero Expr.splitZero_injective
  | succ n ih =>
    have hp := (small_fin hk 3).prod (regular_pos hk) (ih.prod (regular_pos hk) ih)
    exact SmallFor.of_injective (regular_pos hk) (((small_unit hk).sum hX).sum hp)
      Expr.splitSucc Expr.splitSucc_injective

theorem small_expr {k : O} (hk : UncountableRegular k) {X : Type}
    (hX : SmallFor k X) : SmallFor k (Expr X) := by
  have hSigma := (small_nat hk).sigma (small_expr_bounded hk hX)
  apply SmallFor.of_injective (regular_pos hk) hSigma (fun c => ⟨c.height, ⟨c, Nat.le_refl _⟩⟩)
  intro x y h
  exact congrArg (fun p : (n : Nat) × Expr.Bounded X n => p.2.1) h

end
end OCF.Denis
