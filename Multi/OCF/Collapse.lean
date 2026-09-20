import Multi.OCF.Hartogs
import Multi.OCF.Arithmetic

namespace OCF

universe u

open Ordinal

/-- A finite expression in the three arguments of a closure operation. -/
inductive ClosureCode (X : Type u) : Type u where
  | leaf (x : X)
  | node (index argument tail : ClosureCode X)

structure CollapseStage where
  closed : Ordinal.{u} → Ordinal.{u} → Prop
  collapse : Ordinal.{u} → Ordinal.{u}

/-- The closure at one stage, using only collapse values at smaller arguments. -/
inductive StageClosure (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    Ordinal.{u} → Prop where
  | base (b : Ordinal.{u}) (h : b < Ω v) : StageClosure Ω a previous v b
  | step (index argument tail : Ordinal.{u}) (ha : argument < a)
      (hi : StageClosure Ω a previous v index)
      (hx : StageClosure Ω a previous v argument)
      (ht : StageClosure Ω a previous v tail)
      (hr : (previous argument ha).closed index argument) :
      StageClosure Ω a previous v ((previous argument ha).collapse index + tail)

namespace Collapse

noncomputable def evaluate (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u})
    (c : ClosureCode (representative (Ω v)).Carrier) : Ordinal.{u} := by
  classical
  exact match c with
    | .leaf x => type ((representative (Ω v)).below x)
    | .node ci cx ct =>
      if h : evaluate Ω a previous v cx < a then
        (previous (evaluate Ω a previous v cx) h).collapse (evaluate Ω a previous v ci) +
          evaluate Ω a previous v ct
      else 0

theorem closed_has_code (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v b : Ordinal.{u})
    (h : StageClosure Ω a previous v b) :
    ∃ c, evaluate Ω a previous v c = b := by
  induction h with
  | base b hb =>
    cases initial_surjective (Ω v) b hb with
    | intro x hx => exact Exists.intro (.leaf x) hx.symm
  | step index argument tail ha hi hx ht hr ihi ihx iht =>
    cases ihi with
    | intro ci hci =>
      cases ihx with
      | intro cx hcx =>
        cases iht with
        | intro ct hct =>
          refine Exists.intro (.node ci cx ct) ?_
          rw [evaluate, hcx, hci, hct, dite_eq_left ha]

theorem missing_exists (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    ∃ b, b < hartogs (ClosureCode (representative (Ω v)).Carrier) ∧
      ¬ StageClosure Ω a previous v b := by
  cases exists_not_range_lt_hartogs (evaluate Ω a previous v) with
  | intro b hb =>
    refine Exists.intro b (And.intro hb.1 ?_)
    intro hc
    exact hb.2 (closed_has_code Ω a previous v b hc)

theorem least_missing_exists (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    ∃ b, (¬ StageClosure Ω a previous v b) ∧
      ∀ c, c < b → ¬ ¬ StageClosure Ω a previous v c := by
  apply Ordinal.exists_min
  cases missing_exists Ω a previous v with
  | intro b hb => exact Exists.intro b hb.2

noncomputable def makeStage (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) : CollapseStage.{u} where
  closed v b := StageClosure Ω a previous v b
  collapse v := Classical.choose (least_missing_exists Ω a previous v)

theorem makeStage_not_mem (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    ¬ (makeStage Ω a previous).closed v ((makeStage Ω a previous).collapse v) :=
  (Classical.choose_spec (least_missing_exists Ω a previous v)).1

theorem makeStage_lt_mem (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v b : Ordinal.{u})
    (h : b < (makeStage Ω a previous).collapse v) :
    (makeStage Ω a previous).closed v b :=
  Classical.byContradiction
    ((Classical.choose_spec (least_missing_exists Ω a previous v)).2 b h)

theorem makeStage_lower_bound (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    Ω v ≤ (makeStage Ω a previous).collapse v := by
  apply (not_lt_iff_le _ _).mp
  intro h
  exact makeStage_not_mem Ω a previous v (StageClosure.base _ h)

theorem makeStage_upper_bound (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u})
    (previous : (b : Ordinal.{u}) → b < a → CollapseStage.{u}) (v : Ordinal.{u}) :
    (makeStage Ω a previous).collapse v < hartogs (ClosureCode (representative (Ω v)).Carrier) := by
  cases missing_exists Ω a previous v with
  | intro b hb =>
    have hle : (makeStage Ω a previous).collapse v ≤ b := by
      apply (not_lt_iff_le _ _).mp
      intro h
      exact hb.2 (makeStage_lt_mem Ω a previous v b h)
    exact lt_of_le_of_lt hle hb.1

noncomputable def stages (Ω : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → CollapseStage.{u} :=
  lt_wellFounded.fix (fun a previous => makeStage Ω a previous)

theorem stages_eq (Ω : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    stages Ω a = makeStage Ω a (fun b _ => stages Ω b) :=
  WellFounded.fix_eq lt_wellFounded _ a

def C (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u}) : Prop :=
  (stages Ω a).closed v b

noncomputable def psi (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u}) : Ordinal.{u} :=
  (stages Ω a).collapse v

theorem C_iff (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u}) :
    C Ω v a b ↔ StageClosure Ω a (fun c _ => stages Ω c) v b := by
  unfold C
  rw [stages_eq]
  exact Iff.intro (fun h => h) (fun h => h)

theorem C_base (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u}) (h : b < Ω v) :
    C Ω v a b := (C_iff Ω v a b).mpr (StageClosure.base b h)

theorem C_step (Ω : Ordinal.{u} → Ordinal.{u}) (v a index argument tail : Ordinal.{u})
    (ha : argument < a) (hi : C Ω v a index) (hx : C Ω v a argument)
    (ht : C Ω v a tail) (hr : C Ω index argument argument) :
    C Ω v a (psi Ω index argument + tail) := by
  apply (C_iff Ω v a _).mpr
  exact StageClosure.step index argument tail ha
    ((C_iff Ω v a index).mp hi) ((C_iff Ω v a argument).mp hx)
    ((C_iff Ω v a tail).mp ht) hr

theorem psi_not_mem (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u}) :
    ¬ C Ω v a (psi Ω v a) := by
  unfold C psi
  rw [stages_eq]
  exact makeStage_not_mem Ω a _ v

theorem lt_psi_mem (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u})
    (h : b < psi Ω v a) : C Ω v a b := by
  unfold psi at h
  rw [stages_eq] at h
  unfold C
  rw [stages_eq]
  exact makeStage_lt_mem Ω a _ v b h

theorem psi_lower_bound (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u}) :
    Ω v ≤ psi Ω v a := by
  unfold psi
  rw [stages_eq]
  exact makeStage_lower_bound Ω a _ v

theorem psi_upper_bound (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u}) :
    psi Ω v a < hartogs (ClosureCode (representative (Ω v)).Carrier) := by
  unfold psi
  rw [stages_eq]
  exact makeStage_upper_bound Ω a _ v

theorem C_mono (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u})
    (hab : a ≤ b) (x : Ordinal.{u}) (hx : C Ω v a x) : C Ω v b x := by
  have h := (C_iff Ω v a x).mp hx
  clear hx
  induction h with
  | base x hx => exact C_base Ω v b x hx
  | step index argument tail ha hi hx ht hr ihi ihx iht =>
    exact C_step Ω v b index argument tail (lt_of_lt_of_le ha hab) ihi ihx iht hr

theorem psi_mono (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u}) (hab : a ≤ b) :
    psi Ω v a ≤ psi Ω v b := by
  apply (not_lt_iff_le _ _).mp
  intro h
  exact psi_not_mem Ω v b (C_mono Ω v a b hab _ (lt_psi_mem Ω v a _ h))

theorem psi_strict (Ω : Ordinal.{u} → Ordinal.{u}) (v a b : Ordinal.{u})
    (hv : v < Ω v) (hzero : 0 < Ω v) (hab : a < b) (ha : C Ω v a a) :
    psi Ω v a < psi Ω v b := by
  have hmem : C Ω v b (psi Ω v a) := by
    have h := C_step Ω v b v a 0 hab (C_base Ω v b v hv)
      (C_mono Ω v a b (Or.inl hab) a ha) (C_base Ω v b 0 hzero) ha
    rw [add_zero] at h
    exact h
  cases psi_mono Ω v a b (Or.inl hab) with
  | inl h => exact h
  | inr h =>
    rw [h] at hmem
    exact False.elim (psi_not_mem Ω v b hmem)

theorem C_zero_iff (Ω : Ordinal.{u} → Ordinal.{u}) (v b : Ordinal.{u}) :
    C Ω v 0 b ↔ b < Ω v := by
  apply Iff.intro
  · intro h
    cases (C_iff Ω v 0 b).mp h with
    | base _ hb => exact hb
    | step index argument tail ha hi hx ht hr =>
      exact False.elim (not_lt_zero argument ha)
  · exact C_base Ω v 0 b

theorem psi_zero (Ω : Ordinal.{u} → Ordinal.{u}) (v : Ordinal.{u}) : psi Ω v 0 = Ω v := by
  apply le_antisymm
  · apply (not_lt_iff_le (Ω v) (psi Ω v 0)).mp
    intro h
    exact lt_irrefl (Ω v) ((C_zero_iff Ω v (Ω v)).mp (lt_psi_mem Ω v 0 (Ω v) h))
  · exact psi_lower_bound Ω v 0

theorem C_add_closed (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u})
    (hv : AddPrincipal (Ω v)) (x y : Ordinal.{u}) (hx : C Ω v a x) (hy : C Ω v a y) :
    C Ω v a (x + y) := by
  have h := (C_iff Ω v a x).mp hx
  clear hx
  induction h generalizing y with
  | base x hx =>
    cases lt_total y (Ω v) with
    | inl hyv => exact C_base Ω v a (x + y) (hv x y hx hyv)
    | inr hrest =>
      have hvy : Ω v ≤ y := by
        cases hrest with
        | inl hyv => exact Or.inr hyv.symm
        | inr hvy => exact Or.inl hvy
      rw [hv.absorb_of_le hx hvy]
      exact hy
  | step index argument tail ha hi hx ht hr ihi ihx iht =>
    rw [add_assoc]
    exact C_step Ω v a index argument (tail + y) ha
      ((C_iff Ω v a index).mpr hi) ((C_iff Ω v a argument).mpr hx) (iht y hy) hr

theorem psi_principal (Ω : Ordinal.{u} → Ordinal.{u}) (v a : Ordinal.{u})
    (hv : AddPrincipal (Ω v)) : AddPrincipal (psi Ω v a) := by
  intro x y hx hy
  cases lt_total (x + y) (psi Ω v a) with
  | inl h => exact h
  | inr hrest =>
    have hle : psi Ω v a ≤ x + y := by
      cases hrest with
      | inl h => exact Or.inr h.symm
      | inr h => exact Or.inl h
    cases le_add_cases x y (psi Ω v a) hle (lt_asymm hx) with
    | intro d hd =>
      have hmem := C_add_closed Ω v a hv x d (lt_psi_mem Ω v a x hx)
        (lt_psi_mem Ω v a d (lt_of_le_of_lt hd.1 hy))
      rw [← hd.2] at hmem
      exact False.elim (psi_not_mem Ω v a hmem)

end Collapse
end OCF
