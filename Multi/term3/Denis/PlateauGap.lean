import Multi.term3.Denis.IndexGap

/-! Argument plateaus of proper collapses.

If `psi l c` equals a proper collapse `psi k b`, then `c ≤ b`, the
collapse at `k` is already constant on `[c, b]`, and the defining closure
`C(b, psi k b)` has no element in `[c, b)`. Consequently that closure
is generated with the smaller cutoff `c`; in particular `b` itself is.
So the proper argument is the least element of its own closure above any
other presentation argument. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_proper_plateau (s : Supply) (k b l c : O)
    (hk : RegularIndex s k) (hl : RegularIndex s l)
    (hkC : C s b (psi s k b) k) (hbC : C s b (psi s k b) b)
    (heq : psi s l c = psi s k b) :
    c ≤ b ∧ psi s k c = psi s k b ∧
      ∀ d, C s b (psi s k b) d → c ≤ d → d < b → False := by
  have hcb : c ≤ b := by
    apply (not_lt_iff_le _ _).mp
    intro hbc
    exact psi_ne_of_argument_lt s k b l c hk hl hbc hkC hbC heq.symm
  have hlt := psi_lt s k b (regularIndex_regular s k hk)
  have hkc : psi s k c = psi s k b := by
    rcases lt_total l k with hlk | hlk | hkl
    · apply le_antisymm (psi_mono s k c b hcb)
      rw [← heq]
      exact psi_mono_index s l k c (Or.inl hlk)
    · rw [← hlk]
      exact hlk ▸ heq
    · rw [psi_index_plateau s k l c (by rw [heq]; exact Or.inl hlt) (Or.inl hkl)]
      exact heq
  refine ⟨hcb, hkc, ?_⟩
  intro d hd hcd hdb
  have hkd : psi s k d = psi s k b :=
    le_antisymm (psi_mono s k d b (Or.inl hdb)) (hkc ▸ psi_mono s k c d hcd)
  have hval := C_collapse s b _ k d hdb hk hkC hd
  rw [hkd] at hval
  exact lt_irrefl _ (psi_closed s k b _ hval hlt)

/-- A closure whose elements below the cutoff all lie below `c` is
already generated with cutoff `c`. -/
theorem C_cutoff_restrict (s : Supply) (b c gamma : O)
    (hgap : ∀ d, C s b gamma d → d < b → d < c) (x : O) (hx : C s b gamma x) :
    C s c gamma x := by
  have h := C_least s b gamma (fun y => C s c gamma y ∧ C s b gamma y)
    ⟨C_zero s c gamma, C_zero s b gamma⟩
    (fun y hy => ⟨C_seed s c gamma y hy, C_seed s b gamma y hy⟩)
    (fun y z hy hz => ⟨C_add s c gamma y z hy.1 hz.1, C_add s b gamma y z hy.2 hz.2⟩)
    (fun y z hy hz => ⟨C_index s c gamma y z hy.1 hz.1, C_index s b gamma y z hy.2 hz.2⟩)
    (fun k e he hk hkP heP => ⟨C_collapse s c gamma k e (hgap e heP.2 he) hk hkP.1 heP.1,
      C_collapse s b gamma k e he hk hkP.2 heP.2⟩) x hx
  exact h.1

/-- The proper argument and its index are generated with the cutoff of
any other presentation argument. -/
theorem proper_parameters_at_presentation (s : Supply) (k b l c : O)
    (hk : RegularIndex s k) (hl : RegularIndex s l)
    (hkC : C s b (psi s k b) k) (hbC : C s b (psi s k b) b)
    (heq : psi s l c = psi s k b) :
    C s c (psi s k b) k ∧ C s c (psi s k b) b := by
  obtain ⟨_, _, hgap⟩ := psi_proper_plateau s k b l c hk hl hkC hbC heq
  have hres : ∀ d, C s b (psi s k b) d → d < b → d < c := by
    intro d hd hdb
    apply lt_of_not_ge'
    intro hcd
    exact hgap d hd hcd hdb
  exact ⟨C_cutoff_restrict s b c _ hres k hkC, C_cutoff_restrict s b c _ hres b hbC⟩

end
end OCF.Denis
