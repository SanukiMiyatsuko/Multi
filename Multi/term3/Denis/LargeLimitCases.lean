import Multi.term3.Denis.RepresentedClosure

/-! The large limit step when the collapse is not constant below its
argument.

If `psi k c < psi k a` for every `c < a`, then `psi k` is a monotone map
from `a` into `psi k a` which is cofinal by continuity at limits. The two
cofinalities agree, and `i ↦ psi k (f i) + i` is a strictly increasing
covering sequence for any covering sequence `f` of `a`. Its values at
normal indices are normal by the closure of represented ordinals under
collapses. -/

namespace OCF.Denis
open Ordinal
noncomputable section

/-- A monotone map from `a` into `b`, cofinal in `b`, identifies the two
cofinalities. -/
theorem cofinality_eq_of_monotone (a b : O) (ha : IsLimit a) (hb : IsLimit b) (F : O → O)
    (hmono : ∀ x y, x ≤ y → F x ≤ F y) (hbelow : ∀ x, x < a → F x < b)
    (hcof : ∀ y, y < b → ∃ x, x < a ∧ y < F x) :
    cofinality b hb = cofinality a ha := by
  classical
  apply le_antisymm
  · obtain ⟨fa, hfa⟩ := (cofinality_spec a ha).1
    apply cofinality_le b hb
    refine ⟨fun i => F (fa i), fun i hi => hbelow _ (hfa.below i hi), fun y hy => ?_⟩
    obtain ⟨x, hxa, hyx⟩ := hcof y hy
    obtain ⟨i, hi, hxi⟩ := hfa.cofinal x hxa
    exact ⟨i, hi, lt_of_lt_of_le hyx (hmono x (fa i) (Or.inl hxi))⟩
  · obtain ⟨h, hh⟩ := (cofinality_spec b hb).1
    apply cofinality_le a ha
    let g : O → O := fun j =>
      if hj : j < cofinality b hb then Classical.choose (hcof (h j) (hh.below j hj)) else 0
    have hg : ∀ j, j < cofinality b hb → g j < a ∧ h j < F (g j) := by
      intro j hj
      simp only [g, hj, ↓reduceDIte]
      exact Classical.choose_spec (hcof (h j) (hh.below j hj))
    refine ⟨g, fun j hj => (hg j hj).1, fun c hc => ?_⟩
    obtain ⟨j, hj, hcj⟩ := hh.cofinal (F c) (hbelow c hc)
    refine ⟨j, hj, lt_of_not_ge' (fun hle => ?_)⟩
    exact (not_lt_iff_le _ _).mpr (hmono _ _ hle) (lt_trans _ _ _ hcj (hg j hj).2)

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

/-- Collapses are continuous at limit arguments. -/
theorem psi_limit_cofinal (s : OCF.Denis.Supply) (k a : OCF.Denis.O) (ha : OCF.Denis.IsLimit a)
    (y : OCF.Denis.O) (hy : y < OCF.Denis.psi s k a) :
    ∃ c, c < a ∧ y < OCF.Denis.psi s k c := by
  apply Classical.byContradiction
  intro hnot
  apply (not_lt_iff_le _ _).mpr _ hy
  apply OCF.Denis.psi_limit_le s k a y ha
  intro c hc
  exact (not_lt_iff_le _ _).mp (fun hlt => hnot ⟨c, hc, hlt⟩)

/-- The large limit step when the collapse is strictly below its value at
every smaller argument. Only a covering sequence of the argument is used. -/
theorem hasCoveringSequence_psi_nonisolated (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.IsLimit (denote s a))
    (hnoniso : ∀ c, c < denote s a →
      OCF.Denis.psi s (denote s k) c < OCF.Denis.psi s (denote s k) (denote s a))
    (haCov : HasCoveringSequence s (denote s a)) :
    HasCoveringSequence s (denote s (.psi k a)) := by
  intro hg
  obtain ⟨hτ, f, hf⟩ := haCov ha
  have hk : IsNormal s k := by cases hn; assumption
  have hreg : OCF.Denis.RegularIndex s (denote s k) := by cases hn; assumption
  have hkrep : Represented s (denote s k) := ⟨k, hk, rfl⟩
  have hprin := OCF.Denis.psi_addPrincipal s (denote s k) (denote s a)
    (OCF.Denis.regularIndex_regular s _ hreg)
  have hmono : ∀ x y, x ≤ y → OCF.Denis.psi s (denote s k) x ≤ OCF.Denis.psi s (denote s k) y :=
    fun x y hxy => OCF.Denis.psi_mono s _ x y hxy
  have hcf : OCF.Denis.cofinality (denote s (.psi k a)) hg = OCF.Denis.cofinality (denote s a) ha :=
    OCF.Denis.cofinality_eq_of_monotone _ _ ha hg _ hmono hnoniso
      (psi_limit_cofinal s (denote s k) (denote s a) ha)
  have hτle : OCF.Denis.cofinality (denote s a) ha ≤ denote s (.psi k a) := by
    rw [← hcf]
    exact OCF.Denis.cofinality_le_self _ hg
  have hfund := hf.normalSequence.fundamental
  rw [hcf]
  refine ⟨hτ, fun i => OCF.Denis.psi s (denote s k) (f i) + i, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
  · intro i hi
    exact hprin _ _ (hnoniso _ (hfund.below i hi)) (OCF.Ordinal.lt_of_lt_of_le hi hτle)
  · intro i j hij hj
    exact OCF.Ordinal.lt_of_le_of_lt
      (add_mono_left (hmono _ _ (Or.inl (hfund.strict i j hij hj))) i)
      (add_lt_add_right _ hij)
  · intro x hx
    obtain ⟨c, hca, hxc⟩ := psi_limit_cofinal s (denote s k) (denote s a) ha x hx
    obtain ⟨i, hi, hci⟩ := hfund.cofinal c hca
    exact ⟨i, hi, OCF.Ordinal.lt_of_lt_of_le hxc
      (OCF.Ordinal.le_trans (hmono _ _ (Or.inl hci)) (le_add _ i))⟩
  · intro i hi hirep
    exact represented_add s _ _
      (represented_psi s _ _ hkrep (hf.normalSequence.normal i hi hirep) hreg) hirep
  · intro x hxrep hx
    obtain ⟨c, hcrep, hca, hxc⟩ :=
      represented_limit_collapse_interpolation s _ _ x hreg ha hxrep hx
    obtain ⟨i, hirep, hi, hci⟩ := hf.cofinal_normal c hcrep hca
    exact ⟨i, hirep, hi, OCF.Ordinal.lt_of_lt_of_le hxc
      (OCF.Ordinal.le_trans (hmono _ _ (Or.inl hci)) (le_add _ i))⟩

/-- The remaining large limit case: the collapse already takes its value at
a smaller argument, so it is constant on a final segment below the
argument. This is an explicit proposition, not an axiom. -/
def IsolatedLargeLimitStep (s : OCF.Denis.Supply) : Prop :=
  ∀ k a, IsNormal s (.psi k a) → OCF.Denis.IsLimit (denote s a) →
    ¬ OCF.Denis.UncountableRegular (denote s a) → denote s k ≤ denote s a →
    OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) →
    (∃ c, c < denote s a ∧ OCF.Denis.psi s (denote s k) c = denote s (.psi k a)) →
    (∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasCoveringSequence s (denote s u)) →
    HasCoveringSequence s (denote s (.psi k a))

theorem largeLimitCoveringStep_of_isolated (s : OCF.Denis.Supply) (h : IsolatedLargeLimitStep s) :
    LargeLimitCoveringStep s := by
  intro k a hn ha hnreg hka hK ih
  by_cases hiso : ∃ c, c < denote s a ∧ OCF.Denis.psi s (denote s k) c = denote s (.psi k a)
  · exact h k a hn ha hnreg hka hK hiso ih
  · have hanorm : IsNormal s a := by cases hn; assumption
    apply hasCoveringSequence_psi_nonisolated s k a hn ha _
      (ih a (by change sizeOf a < sizeOf (Term.psi k a); simp; omega) hanorm)
    intro c hc
    rcases OCF.Denis.psi_mono s (denote s k) c _ (Or.inl hc) with hlt | heq
    · exact hlt
    · exact absurd ⟨c, hc, heq⟩ hiso

/-- Every normal term has a covering sequence once the isolated large
limit case is settled. -/
theorem normal_hasCoveringSequence_of_isolated (s : OCF.Denis.Supply) (h : IsolatedLargeLimitStep s)
    (t : Term) (ht : IsNormal s t) : HasCoveringSequence s (denote s t) :=
  normal_hasCoveringSequence_of_large_limit s (largeLimitCoveringStep_of_isolated s h) t ht

end
end T.Correspondence.Denis.Covering
