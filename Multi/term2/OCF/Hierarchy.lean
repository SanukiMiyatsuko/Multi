import Multi.term2.OCF.Collapse
import Multi.term2.OCF.Principal

namespace OCF.Collapse

universe u

open Ordinal

noncomputable section

local instance : DecidableEq Ordinal.{u} := fun a b => Classical.propDecidable (a = b)

/-- A bound for every earlier collapse range, together with the current index. -/
def hierarchyBound (a : Ordinal.{u}) (previous : (b : Ordinal.{u}) → b < a → Ordinal.{u}) :
    Ordinal.{u} :=
  sup (fun x : Option (representative a).Carrier =>
    match x with
    | none => a
    | some x => hartogs (ClosureCode
        (representative (previous (type ((representative a).below x)) (initial_lt a x))).Carrier))

/-- An interpretation hierarchy with enough space for the finite closure codes. -/
def hierarchy : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun a previous =>
    if a = 0 then succ 0 else principalHull (hierarchyBound a previous))

theorem hierarchy_eq (a : Ordinal.{u}) :
    hierarchy a = if a = 0 then succ 0
      else principalHull (hierarchyBound a (fun b _ => hierarchy b)) :=
  WellFounded.fix_eq lt_wellFounded _ a

theorem hierarchy_zero : hierarchy (0 : Ordinal.{u}) = succ 0 := by
  rw [hierarchy_eq, ite_eq_left rfl]

theorem hierarchy_nonzero (a : Ordinal.{u}) (ha : a ≠ 0) :
    hierarchy a = principalHull (hierarchyBound a (fun b _ => hierarchy b)) := by
  rw [hierarchy_eq, ite_eq_right ha]

theorem index_lt_hierarchy (a : Ordinal.{u}) : a < hierarchy a := by
  by_cases ha : a = 0
  · cases ha
    rw [hierarchy_zero]
    exact lt_succ_self 0
  · rw [hierarchy_nonzero a ha]
    exact lt_of_le_of_lt (le_sup _ none) (lt_principalHull _)

theorem hierarchy_pos (a : Ordinal.{u}) : 0 < hierarchy a :=
  lt_of_le_of_lt (zero_le a) (index_lt_hierarchy a)

theorem hierarchy_principal (a : Ordinal.{u}) : AddPrincipal (hierarchy a) := by
  by_cases ha : a = 0
  · cases ha
    rw [hierarchy_zero]
    exact succ_zero_principal
  · rw [hierarchy_nonzero a ha]
    exact principalHull_principal _

theorem hierarchy_gap (a b : Ordinal.{u}) (hab : a < b) :
    hartogs (ClosureCode (representative (hierarchy a)).Carrier) ≤ hierarchy b := by
  have hb : b ≠ 0 := by
    intro h
    rw [h] at hab
    exact not_lt_zero a hab
  rw [hierarchy_nonzero b hb]
  cases initial_surjective b a hab with
  | intro x hx =>
    have hbound : hartogs (ClosureCode (representative (hierarchy a)).Carrier) ≤
        hierarchyBound b (fun c _ => hierarchy c) := by
      rw [hx]
      exact le_sup _ (some x)
    exact le_trans hbound (Or.inl (lt_principalHull _))

theorem hierarchy_strict (a b : Ordinal.{u}) (hab : a < b) : hierarchy a < hierarchy b := by
  have h : hierarchy a < hartogs (ClosureCode (representative (hierarchy a)).Carrier) := by
    apply lt_hartogs_of_injective (hierarchy a) ClosureCode.leaf
    intro x y hxy
    cases hxy
    rfl
  exact lt_of_lt_of_le h (hierarchy_gap a b hab)

theorem psi_lt_hierarchy (v w a : Ordinal.{u}) (hvw : v < w) :
    psi hierarchy v a < hierarchy w :=
  lt_of_lt_of_le (psi_upper_bound hierarchy v a) (hierarchy_gap v w hvw)

theorem psi_index_strict (v w a b : Ordinal.{u}) (hvw : v < w) :
    psi hierarchy v a < psi hierarchy w b :=
  lt_of_lt_of_le (psi_lt_hierarchy v w a hvw) (psi_lower_bound hierarchy w b)

theorem psi_hierarchy_principal (v a : Ordinal.{u}) : AddPrincipal (psi hierarchy v a) :=
  psi_principal hierarchy v a (hierarchy_principal v)

theorem psi_argument_strict (v a b : Ordinal.{u}) (hab : a < b) (ha : C hierarchy v a a) :
    psi hierarchy v a < psi hierarchy v b :=
  psi_strict hierarchy v a b (index_lt_hierarchy v) (hierarchy_pos v) hab ha

end
end OCF.Collapse
