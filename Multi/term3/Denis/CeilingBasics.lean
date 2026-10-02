import Multi.term3.Denis.CollapseContinuity

/-! Ceilings in a closure and the comparison of `I` values.

`IsCeil s c gamma y t` says that `t` is the least element of `C(c, gamma)`
above `y`. `IsSep s c gamma k y t` says that `t` is the least collapse
value `psi k d` above `y`, with `d < c` in `C(c, gamma)`. -/

namespace OCF.Denis
open Ordinal
noncomputable section

/-- Jäger 3.3: the three ways one `I` value lies below another. -/
theorem I_lt_cases (s : Supply) (r z q w : O) (h : I s r z < I s q w) :
    (r < q ∧ z < I s q w) ∨ (r = q ∧ z < w) ∨ (q < r ∧ I s r z < w) := by
  rcases lt_total r q with hrq | rfl | hqr
  · refine Or.inl ⟨hrq, ?_⟩
    rw [← I_rank_fixed s r q w hrq] at h
    exact (I_lt_iff s r _ _).mp h
  · exact Or.inr (Or.inl ⟨rfl, (I_lt_iff s r _ _).mp h⟩)
  · refine Or.inr (Or.inr ⟨hqr, ?_⟩)
    rw [← I_rank_fixed s q r z hqr] at h
    exact (I_lt_iff s q _ _).mp h

def IsCeil (s : Supply) (c gamma y t : O) : Prop :=
  C s c gamma t ∧ y ≤ t ∧ ∀ d, C s c gamma d → y ≤ d → t ≤ d

theorem IsCeil.exists (s : Supply) (c gamma y : O) (h : ∃ d, C s c gamma d ∧ y ≤ d) :
    ∃ t, IsCeil s c gamma y t :=
  ⟨least _ h, (least_spec _ h).1.1, (least_spec _ h).1.2, fun _ hd hyd => least_le _ h ⟨hd, hyd⟩⟩

theorem IsCeil.unique {s : Supply} {c gamma y t t' : O} (h : IsCeil s c gamma y t)
    (h' : IsCeil s c gamma y t') : t = t' :=
  le_antisymm (h.2.2 t' h'.1 h'.2.1) (h'.2.2 t h.1 h.2.1)

theorem IsCeil.gap {s : Supply} {c gamma y t : O} (h : IsCeil s c gamma y t)
    (d : O) (hd : C s c gamma d) (hdt : d < t) : d < y :=
  lt_of_not_ge' (fun hyd => (not_lt_iff_le _ _).mpr (h.2.2 d hd hyd) hdt)

theorem IsCeil.of_mem {s : Supply} {c gamma y t : O} (h : IsCeil s c gamma y t)
    (hy : C s c gamma y) : t = y :=
  le_antisymm (h.2.2 y hy (le_refl y)) h.2.1

theorem IsCeil.self {s : Supply} {c gamma y : O} (hy : C s c gamma y) : IsCeil s c gamma y y :=
  ⟨hy, le_refl y, fun _ _ hyd => hyd⟩

/-- A ceiling above an element of the closure is shifted by that element. -/
theorem IsCeil.add_left {s : Supply} {c gamma u w t : O} (hu : C s c gamma u)
    (h : IsCeil s c gamma (u + w) t) : ∃ t', IsCeil s c gamma w t' ∧ t = u + t' := by
  have hut : u ≤ t := le_trans (le_add u w) h.2.1
  obtain ⟨t'', ht''⟩ := exists_add_of_le u t hut
  have ht''C : C s c gamma t'' := C_suffix s c gamma t u t'' h.1 ht''
  have hwt : w ≤ t'' := by
    apply (not_lt_iff_le _ _).mp
    intro hlt
    have := add_lt_add_right u hlt
    rw [← ht''] at this
    exact (not_lt_iff_le _ _).mpr h.2.1 this
  obtain ⟨t', ht'⟩ := IsCeil.exists s c gamma w ⟨t'', ht''C, hwt⟩
  refine ⟨t', ht', le_antisymm ?_ ?_⟩
  · exact h.2.2 _ (C_add s c gamma u t' hu ht'.1) (add_mono_right u ht'.2.1)
  · rw [ht'']
    exact add_mono_right u (ht'.2.2 t'' ht''C hwt)

/-- The ceiling of an additively principal element outside the closure is a
normal `I` value with parameters below the element, or a proper collapse. -/
theorem IsCeil.canonical (s : Supply) (c gamma y t : O)
    (hD : ∀ x, C s c gamma x → PC s c gamma x)
    (hy : AddPrincipal y) (hyD : ¬ C s c gamma y) (h : IsCeil s c gamma y t) :
    (∃ r z, t = I s r z ∧ r < y ∧ z < y ∧ C s c gamma r ∧ C s c gamma z ∧ r < t ∧ z < t) ∨
    (∃ k e, t = psi s k e ∧ e < c ∧ ProperCollapse s k e ∧ C s c gamma k ∧ C s c gamma e) := by
  have aux (x : O) (hx : PC s c gamma x) : x = t →
      (∃ r z, t = I s r z ∧ r < y ∧ z < y ∧ C s c gamma r ∧ C s c gamma z ∧ r < t ∧ z < t) ∨
      (∃ k e, t = psi s k e ∧ e < c ∧ ProperCollapse s k e ∧ C s c gamma k ∧
        C s c gamma e) := by
    induction hx with
    | zero =>
      intro heq
      have hy0 : y = 0 := le_antisymm (heq ▸ h.2.1) (zero_le y)
      exact False.elim (hyD (hy0 ▸ C_zero s c gamma))
    | seed hx =>
      intro heq
      exact False.elim (hyD (C_seed s c gamma y (lt_of_le_of_lt h.2.1 (heq ▸ hx))))
    | @add u v hu hv ihu ihv =>
      intro heq
      rcases le_add u v with hu' | hu'
      · rcases right_le_add u v with hv' | hv'
        · rw [heq] at hu' hv'
          have hlt := hy u v (h.gap u hu.sub_C hu') (h.gap v hv.sub_C hv')
          rw [heq] at hlt
          exact False.elim ((not_lt_iff_le _ _).mpr h.2.1 hlt)
        · exact ihv (hv'.trans heq)
      · exact ihu (hu'.trans heq)
    | @index u v hu hv ihu ihv =>
      intro heq
      rcases rank_le_I s u v with hu' | hu'
      · rcases index_le_I s u v with hv' | hv'
        · rw [heq] at hu' hv'
          exact Or.inl ⟨u, v, heq.symm, h.gap u hu.sub_C hu', h.gap v hv.sub_C hv',
            hu.sub_C, hv.sub_C, hu', hv'⟩
        · exact ihv (hv'.trans heq)
      · exact ihu (hu'.trans heq)
    | @collapse k e he hp hk he' _ _ =>
      intro heq
      exact Or.inr ⟨k, e, heq.symm, he, hp, hk.sub_C, he'.sub_C⟩
  exact aux t (hD t h.1) rfl

def IsSep (s : Supply) (c gamma k y t : O) : Prop :=
  ∃ d, d < c ∧ C s c gamma d ∧ t = psi s k d ∧ y < t ∧
    ∀ d', d' < c → C s c gamma d' → y < psi s k d' → t ≤ psi s k d'

theorem IsSep.unique {s : Supply} {c gamma k y t t' : O} (h : IsSep s c gamma k y t)
    (h' : IsSep s c gamma k y t') : t = t' := by
  obtain ⟨d, hdc, hd, rfl, hyt, hmin⟩ := h
  obtain ⟨d', hdc', hd', rfl, hyt', hmin'⟩ := h'
  exact le_antisymm (hmin d' hdc' hd' hyt') (hmin' d hdc hd hyt)

end
end OCF.Denis
