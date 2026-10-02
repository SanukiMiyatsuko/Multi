import Multi.term3.Denis.StageBasics

/-! The uniform stage bound.

`UStage s x` says: whenever `x` is isolated in `C(A, psi k A)`, every stage
closure `C(y, psi k y)` with `y < A` is bounded below `x` by a single
ordinal `w < x`. The same `w` lies in every closure which contains `x`, `y`
and `k` and whose cutoff exceeds `y`; in particular it is denoted by a
normal term and lies in `C(A, psi k A)`.

This file proves the base case (regular indices) and the propagation
through sums and through `I` at limit arguments. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def UStage (s : Supply) (x : O) : Prop :=
  ∀ k A y, RegularIndex s k → C s A (psi s k A) x → IsoIn s A (psi s k A) x → y < A →
    ∃ w, w < x ∧ (∀ b, C s y (psi s k y) b → b < x → b < w) ∧
      ∀ A' B', C s A' B' x → C s A' B' y → C s A' B' k → y < A' → C s A' B' w

theorem ustage_zero (s : Supply) : UStage s 0 := by
  intro k A y _ _ hiso _
  exact False.elim (hiso.1.1 rfl)

/-- Base case: a regular index is bounded by the collapse of the stage. -/
theorem ustage_regular (s : Supply) (x : O) (hx : RegularIndex s x) : UStage s x := by
  intro k A y _ hxY hiso _
  have hreg := regularIndex_regular s x hx
  have hkx : k ≤ x := hiso.index_le hxY
  refine ⟨psi s x y, psi_lt s x y hreg, ?_, ?_⟩
  · intro b hb hbx
    exact psi_closed s x y b (C_mono_seed s y _ _ (psi_mono_index s k x y hkx) b hb) hbx
  · intro A' B' hxZ hyZ _ hyA'
    exact C_collapse s A' B' x y hyA' hx hxZ hyZ

/-- Sums: the bound of the tail, shifted by the head. -/
theorem ustage_sum (s : Supply) (p q : O) (hq0 : 0 < q)
    (hhead : ∀ A' B', C s A' B' (p + q) → C s A' B' p) (ih : UStage s q) :
    UStage s (p + q) := by
  intro k A y hk hxY hiso hyA
  have hpY := hhead A _ hxY
  have hqY := C_suffix s A _ (p + q) p q hxY rfl
  have hpx : p < p + q := by
    have h := add_lt_add_right p hq0
    rwa [add_zero] at h
  have hcancel : ∀ u v, p + u < p + v → u < v := by
    intro u v h
    apply lt_of_not_ge'
    intro hvu
    exact (not_lt_iff_le _ _).mpr (add_mono_right p hvu) h
  have hqiso : IsoIn s A (psi s k A) q := by
    obtain ⟨hlim, c, hcx, hc⟩ := hiso
    refine ⟨⟨fun h => ?_, fun ⟨q', hq'⟩ => ?_⟩, ?_⟩
    · rw [h] at hq0
      exact lt_irrefl _ hq0
    · apply hlim.2
      exact ⟨p + q', by rw [hq', add_succ]⟩
    · have hpc : p ≤ c := by
        apply (not_lt_iff_le _ _).mp
        intro hcp
        exact hc p hpY (Or.inl hcp) hpx
      obtain ⟨c', hc'⟩ := exists_add_of_le p c hpc
      subst hc'
      refine ⟨c', hcancel _ _ hcx, fun d hd hcd hdq => ?_⟩
      exact hc (p + d) (C_add s A _ p d hpY hd) (add_mono_right p hcd) (add_lt_add_right p hdq)
  obtain ⟨w, hwq, hwb, hwZ⟩ := ih k A y hk hqY hqiso hyA
  refine ⟨p + w, add_lt_add_right p hwq, ?_, ?_⟩
  · intro b hb hbx
    by_cases hbp : b < p
    · exact lt_of_lt_of_le hbp (le_add p w)
    · obtain ⟨b', hb'⟩ := exists_add_of_le p b ((not_lt_iff_le _ _).mp hbp)
      subst hb'
      have hb'H := C_suffix s y _ (p + b') p b' hb rfl
      exact add_lt_add_right p (hwb b' hb'H (hcancel _ _ hbx))
  · intro A' B' hxZ hyZ hkZ hyA'
    exact C_add s A' B' p w (hhead A' B' hxZ)
      (hwZ A' B' (C_suffix s A' B' (p + q) p q hxZ rfl) hyZ hkZ hyA')

/-- `I` at a limit argument: the bound of the argument, under `I`. -/
theorem ustage_I_limit (s : Supply) (r z : O) (hz : IsLimit z) (hrl : r < I s r z)
    (hzl : z < I s r z) (ih : UStage s z) : UStage s (I s r z) := by
  intro k A y hk hxY hiso hyA
  obtain ⟨hrY, hzY⟩ := C_normal_index_parameters s A _ r z hrl hzl hxY
  have hziso : IsoIn s A (psi s k A) z := by
    obtain ⟨_, c, hcx, hc⟩ := hiso
    obtain ⟨z0, hz0, hcz0⟩ := I_limit_cofinal s r z c hz hcx
    refine ⟨hz, z0, hz0, fun d hd hz0d hdz => ?_⟩
    exact hc (I s r d) (C_index s A _ r d hrY hd) (le_trans (Or.inl hcz0) (I_mono s r hz0d))
      (I_strict s r hdz)
  obtain ⟨w, hwz, hwb, hwZ⟩ := ih k A y hk hzY hziso hyA
  refine ⟨I s r w, I_strict s r hwz, ?_, ?_⟩
  · intro b hb hbx
    apply lt_of_not_ge'
    intro hwb'
    obtain ⟨z', hwz', hz'z, hlo, hhi⟩ := I_interval_of_lt s r w z b hz hwb' hbx
    have hz'H := C_I_interval s y _ r z' b hb hlo hhi
    exact (not_lt_iff_le _ _).mpr hwz' (hwb z' hz'H hz'z)
  · intro A' B' hxZ hyZ hkZ hyA'
    obtain ⟨hrZ, hzZ⟩ := C_normal_index_parameters s A' B' r z hrl hzl hxZ
    exact C_index s A' B' r w hrZ (hwZ A' B' hzZ hyZ hkZ hyA')

end
end OCF.Denis
