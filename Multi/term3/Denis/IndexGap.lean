import Multi.term3.Denis.ClosureIntervals

/-! A gap lemma for regular values generated from below.

If `G = I r0 z0` with `r0, z0 < gamma`, and no `I` value of parameters
below `gamma` lies in `[gamma, G)`, then any closure element in
`[gamma, G)` forces `G` itself into the closure (seed `beta ≤ gamma`).

Applied to `gamma = psi k b` with `k` in its own defining closure, this
recovers the index of every such collapse from the collapse value, with
no restriction on the argument and no normality assumption on the
presentation used in the closure. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem lt_of_not_ge' {a b : O} (h : ¬ b ≤ a) : a < b := by
  rcases lt_total a b with h1 | h1 | h1
  · exact h1
  · exact False.elim (h (Or.inr h1.symm))
  · exact False.elim (h (Or.inl h1))

theorem C_index_gap (s : Supply) (a beta gamma G r0 z0 : O)
    (hprin : AddPrincipal gamma) (hbeta : beta ≤ gamma)
    (hG : G = I s r0 z0) (hr0 : r0 < gamma) (hz0 : z0 < gamma)
    (hgap : ∀ r z, r < gamma → z < gamma → I s r z < G → I s r z < gamma)
    (y : O) (hy : C s a beta y) (hlo : gamma ≤ y) (hhi : y < G) : C s a beta G := by
  have h := (C_iff s a beta y).mp hy
  clear hy
  induction h with
  | zero => exact False.elim (not_lt_zero r0 (lt_of_lt_of_le hr0 hlo))
  | seed hy => exact False.elim (lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le hy hbeta) hlo))
  | @add u w hu hw ihu ihw =>
    by_cases hu' : gamma ≤ u
    · exact ihu hu' (lt_of_le_of_lt (le_add u w) hhi)
    · by_cases hw' : gamma ≤ w
      · exact ihw hw' (lt_of_le_of_lt (right_le_add u w) hhi)
      · have hul := lt_of_not_ge' hu'
        have hwl := lt_of_not_ge' hw'
        exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo (hprin u w hul hwl)))
  | @index u w hu hw ihu ihw =>
    by_cases hu' : gamma ≤ u
    · exact ihu hu' (lt_of_le_of_lt (rank_le_I s u w) hhi)
    · by_cases hw' : gamma ≤ w
      · exact ihw hw' (lt_of_le_of_lt (index_le_I s u w) hhi)
      · have hul := lt_of_not_ge' hu'
        have hwl := lt_of_not_ge' hw'
        exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo (hgap u w hul hwl hhi)))
  | @collapse k b hb hk hkc hbc ihk ihb =>
    change gamma ≤ psi s k b at hlo
    change psi s k b < G at hhi
    have hreg := regularIndex_regular s k hk
    rcases lt_total k G with hkG | hkG | hGk
    · exact ihk (le_trans hlo (Or.inl (psi_lt s k b hreg))) hkG
    · exact hkG ▸ (C_iff s a beta k).mpr hkc
    · have hmem : C s b (psi s k b) G := by
        rw [hG]
        exact C_index s b _ r0 z0 (C_seed s b _ r0 (lt_of_lt_of_le hr0 hlo))
          (C_seed s b _ z0 (lt_of_lt_of_le hz0 hlo))
      exact False.elim (lt_asymm hhi (psi_closed s k b G hmem hGk))

/-- A regular closure element above the seed has a normal `I`
presentation whose parameters are again closure elements. -/
theorem C_regular_normal_presentation (s : Supply) (a beta k : O)
    (hk : UncountableRegular k) (hbeta : beta ≤ k) (hx : C s a beta k) :
    ∃ r z, k = I s r z ∧ r < k ∧ z < k ∧ C s a beta r ∧ C s a beta z := by
  have hp : AddPrincipal k := fun _ _ hx hy => regular_add_closed hk hx hy
  have aux (y : O) (hy : StageClosure s a (fun b _ => stages s b) beta y) : y = k →
      ∃ r z, k = I s r z ∧ r < k ∧ z < k ∧ C s a beta r ∧ C s a beta z := by
    induction hy with
    | zero =>
      intro heq
      exact False.elim (lt_irrefl _ (heq ▸ regular_pos hk))
    | seed hy =>
      intro heq
      rw [heq] at hy
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le hy hbeta))
    | @add u w hu hw ihu ihw =>
      intro heq
      rcases addPrincipal_suffix hp heq.symm with hw0 | hwk
      · rw [hw0, add_zero] at heq
        exact ihu heq
      · exact ihw hwk
    | @index u w hu hw ihu ihw =>
      intro heq
      rcases rank_le_I s u w with hur | hur
      · rcases index_le_I s u w with hwr | hwr
        · rw [heq] at hur hwr
          exact ⟨u, w, heq.symm, hur, hwr, (C_iff s a beta u).mpr hu, (C_iff s a beta w).mpr hw⟩
        · exact ihw (hwr.trans heq)
      · exact ihu (hur.trans heq)
    | @collapse l c hc hl hlc hcc ihl ihc =>
      intro heq
      change psi s l c = k at heq
      have hk' : UncountableRegular (psi s l c) := by rw [heq]; exact hk
      exact False.elim (psi_not_uncountableRegular s l c hk')
  exact aux k ((C_iff s a beta k).mp hx) rfl

/-- Index recovery for every collapse whose index belongs to its own
defining closure. The argument is unrestricted, and the closure may
generate the value through any other presentation. -/
theorem C_index_of_collapse_value (s : Supply) (k b a beta : O)
    (hk : RegularIndex s k) (hkC : C s b (psi s k b) k)
    (hbeta : beta ≤ psi s k b) (hx : C s a beta (psi s k b)) : C s a beta k := by
  have hreg := regularIndex_regular s k hk
  have hlt : psi s k b < k := psi_lt s k b hreg
  obtain ⟨r0, z0, hkI, hr0k, hz0k, hr0C, hz0C⟩ :=
    C_regular_normal_presentation s b (psi s k b) k hreg (Or.inl hlt) hkC
  apply C_index_gap s a beta (psi s k b) k r0 z0 (psi_addPrincipal s k b hreg) hbeta hkI
    (psi_closed s k b r0 hr0C hr0k) (psi_closed s k b z0 hz0C hz0k) _ _ hx (le_refl _) hlt
  intro r z hr hz hrz
  exact psi_closed s k b _ (C_index s b _ r z (C_seed s b _ r hr) (C_seed s b _ z hz)) hrz

end
end OCF.Denis
