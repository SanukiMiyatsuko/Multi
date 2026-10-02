import Multi.term3.Denis.ProperClosure

/-! Interval recovery for the enumerations `I`.

`C_I_interval` shows that a closure element between two consecutive values
`I r z` and `I r (succ z)` already forces `z` into the closure. No membership
of the rank `r` is required. The same statements are proved for the
Jäger-style closure `PC`, together with the suffix, predecessor and normal
`I` parameter recoveries that the project proved for `C`. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem I_pos (s : Supply) (r b : O) : 0 < I s r b :=
  lt_of_lt_of_le (regular_pos (first_regular s)) (I_lower_bound s r b)

theorem I_isLimit (s : Supply) (r b : O) : IsLimit (I s r b) := by
  refine ⟨fun h => lt_irrefl _ (h ▸ I_pos s r b), ?_⟩
  rintro ⟨c, hc⟩
  have hp := I_addPrincipal s r b
  rw [hc] at hp
  have hc0 := addPrincipal_succ_pred_zero c hp
  have hone : I s r b < omega := by
    rw [hc, hc0]
    exact finite_lt_omega 1
  exact lt_asymm hone (lt_of_lt_of_le (first_regular s).1 (I_lower_bound s r b))

theorem I_lt_iff (s : Supply) (r a b : O) : I s r a < I s r b ↔ a < b := by
  refine ⟨fun h => ?_, I_strict s r⟩
  rcases lt_total a b with hab | rfl | hba
  · exact hab
  · exact False.elim (lt_irrefl _ h)
  · exact False.elim (lt_asymm h (I_strict s r hba))

theorem I_le_iff (s : Supply) (r a b : O) : I s r a ≤ I s r b ↔ a ≤ b := by
  refine ⟨fun h => ?_, I_mono s r⟩
  apply (not_lt_iff_le _ _).mp
  intro hba
  exact (not_lt_iff_le _ _).mpr h (I_strict s r hba)

/-- A value of a higher rank is a fixed point of every lower enumeration. -/
theorem I_rank_fixed (s : Supply) (r q b : O) (h : r < q) : I s r (I s q b) = I s q b := by
  apply le_antisymm _ (index_le_I s r _)
  apply I_limit_le_of_forall s r _ _ (I_isLimit s q b)
  intro c hc
  exact Or.inl (I_lower_rank_closed s r q b c h hc)

theorem I_rank_mono (s : Supply) (r q b : O) (h : r ≤ q) : I s r b ≤ I s q b := by
  rcases h with h | rfl
  · rw [← I_rank_fixed s r q b h]
    exact I_mono s r (index_le_I s q b)
  · exact le_refl _

theorem I_mono_both (s : Supply) {r q a b : O} (hrq : r ≤ q) (hab : a ≤ b) :
    I s r a ≤ I s q b :=
  le_trans (I_mono s r hab) (I_rank_mono s r q b hrq)

theorem succ_lt_I (s : Supply) (r z : O) : succ z < I s r (succ z) := by
  rcases index_le_I s r (succ z) with h | h
  · exact h
  · exact False.elim ((I_isLimit s r (succ z)).2 ⟨z, h.symm⟩)

theorem rank_lt_I_succ (s : Supply) (r z : O) : r < I s r (succ z) :=
  lt_of_le_of_lt (rank_le_I s r 0) (I_strict s r (lt_of_le_of_lt (zero_le z) (lt_succ_self z)))

theorem psi_isLimit_of_ge (s : Supply) (k a r z : O) (hk : RegularIndex s k)
    (h : I s r z ≤ psi s k a) : IsLimit (psi s k a) := by
  have hreg := regularIndex_regular s k hk
  refine ⟨fun h0 => lt_irrefl _ (lt_of_lt_of_le (I_pos s r z) (h0 ▸ h)), ?_⟩
  rintro ⟨c, hc⟩
  have hp := psi_addPrincipal s k a hreg
  rw [hc] at hp
  have hc0 := addPrincipal_succ_pred_zero c hp
  have hone : psi s k a < omega := by
    rw [hc, hc0]
    exact finite_lt_omega 1
  exact lt_asymm hone (lt_of_lt_of_le (first_regular s).1
    (le_trans (I_lower_bound s r z) h))

/-- Interval recovery for `I`: any closure element between consecutive
values `I r z` and `I r (succ z)` forces `z` into the closure. -/
theorem C_I_interval (s : Supply) (cutoff beta r z x : O) (hx : C s cutoff beta x)
    (hlo : I s r z ≤ x) (hhi : x < I s r (succ z)) : C s cutoff beta z := by
  have h := (C_iff s cutoff beta x).mp hx
  clear hx
  induction h with
  | zero => exact False.elim (lt_irrefl _ (lt_of_lt_of_le (I_pos s r z) hlo))
  | seed hy => exact C_seed s cutoff beta z (lt_of_le_of_lt (le_trans (index_le_I s r z) hlo) hy)
  | @add u w hu hw ihu ihw =>
    by_cases hu' : I s r z ≤ u
    · exact ihu hu' (lt_of_le_of_lt (le_add u w) hhi)
    · have hul : u < I s r z := by
        rcases lt_total u (I s r z) with h | h | h
        · exact h
        · exact False.elim (hu' (Or.inr h.symm))
        · exact False.elim (hu' (Or.inl h))
      apply ihw _ (lt_of_le_of_lt (right_le_add u w) hhi)
      apply (not_lt_iff_le _ _).mp
      intro hwl
      exact (not_lt_iff_le _ _).mpr hlo (I_addPrincipal s r z u w hul hwl)
  | @index u w hu hw ihu ihw =>
    rcases lt_total u r with hur | rfl | hru
    · rw [← I_rank_fixed s u r z hur] at hlo
      rw [← I_rank_fixed s u r (succ z) hur] at hhi
      exact ihw ((I_le_iff s u _ _).mp hlo) ((I_lt_iff s u _ _).mp hhi)
    · have hzw := (I_le_iff s u _ _).mp hlo
      have hwz := (lt_succ_iff_le _ _).mp ((I_lt_iff s u _ _).mp hhi)
      exact (le_antisymm hwz hzw) ▸ (C_iff s cutoff beta w).mpr hw
    · have hfix := I_rank_fixed s r u w hru
      rw [← hfix] at hlo hhi
      have hzw := (I_le_iff s r _ _).mp hlo
      have hwz := (lt_succ_iff_le _ _).mp ((I_lt_iff s r _ _).mp hhi)
      rw [← le_antisymm hwz hzw]
      exact C_index s cutoff beta u w ((C_iff s cutoff beta u).mpr hu) ((C_iff s cutoff beta w).mpr hw)
  | @collapse k b hb hk hkc hbc ihk ihb =>
    change I s r z ≤ psi s k b at hlo
    change psi s k b < I s r (succ z) at hhi
    have hreg := regularIndex_regular s k hk
    rcases lt_total k (I s r (succ z)) with hkl | hkl | hlk
    · rcases lt_total k (I s r z) with hkz | hkz | hzk
      · exact False.elim (lt_asymm (lt_of_le_of_lt hlo (psi_lt s k b hreg)) hkz)
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo (hkz ▸ psi_lt s k b hreg)))
      · exact ihk (Or.inl hzk) hkl
    · have hkC := (C_iff s cutoff beta k).mpr hkc
      rw [hkl] at hkC
      exact C_predecessor s cutoff beta z
        (C_normal_index_parameters s cutoff beta r (succ z) (rank_lt_I_succ s r z) (succ_lt_I s r z) hkC).2
    · have hlim := psi_isLimit_of_ge s k b r z hk hlo
      have hxC : C s cutoff beta (psi s k b) :=
        C_collapse s cutoff beta k b hb hk ((C_iff s cutoff beta k).mpr hkc) ((C_iff s cutoff beta b).mpr hbc)
      by_cases hzx : z < psi s k b
      · by_cases hrx : r < psi s k b
        · have hmem := C_index s b (psi s k b) r (succ z) (C_seed s b _ r hrx)
            (C_seed s b _ (succ z) (succ_lt_limit hlim hzx))
          exact False.elim (lt_asymm hhi (psi_closed s k b _ hmem hlk))
        · have hxr : psi s k b ≤ r := (not_lt_iff_le _ _).mp hrx
          have h1 : I s r z ≤ I s r 0 := le_trans hlo (le_trans hxr (rank_le_I s r 0))
          rw [le_antisymm ((I_le_iff s r _ _).mp h1) (zero_le z)]
          exact C_zero s cutoff beta
      · have hxz : psi s k b ≤ z := (not_lt_iff_le _ _).mp hzx
        rw [le_antisymm (le_trans (index_le_I s r z) hlo) hxz]
        exact hxC

/-! Recovery lemmas for the Jäger-style closure. -/

theorem PC_suffix (s : Supply) (a beta x r b : O) (hx : PC s a beta x) (heq : x = r + b) :
    PC s a beta b := by
  induction hx generalizing r b with
  | zero =>
    have hvle : b ≤ (0 : O) := heq ▸ right_le_add r b
    rw [le_antisymm hvle (zero_le b)]
    exact .zero
  | seed hy =>
    have hvle : b ≤ _ := heq ▸ right_le_add r b
    exact .seed (lt_of_le_of_lt hvle hy)
  | @add u v hu hv ihu ihv =>
    rcases lt_total r u with hqu | hqu | huq
    · obtain ⟨c, hc⟩ := exists_add_of_le r u (Or.inl hqu)
      have hcC := ihu r c hc
      have hsum := PC.add hcC hv
      rw [hc, add_assoc] at heq
      exact (add_right_cancel heq) ▸ hsum
    · rw [hqu] at heq
      exact (add_right_cancel heq) ▸ hv
    · obtain ⟨c, hc⟩ := exists_add_of_le u r (Or.inl huq)
      rw [hc, add_assoc] at heq
      exact ihv c b (add_right_cancel heq)
  | @index q c hq hc ihq ihc =>
    rcases addPrincipal_suffix (I_addPrincipal s q c) heq with hz | hz
    · rw [hz]; exact .zero
    · rw [hz]; exact .index hq hc
  | @collapse k c hc hp hk hcc ihk ihc =>
    rcases addPrincipal_suffix (psi_addPrincipal s k c (regularIndex_regular s k hp.1)) heq with hz | hz
    · rw [hz]; exact .zero
    · rw [hz]; exact .collapse hc hp hk hcc

theorem PC_predecessor (s : Supply) (a beta x : O) (hx : PC s a beta (succ x)) : PC s a beta x := by
  have aux (y : O) (hy : PC s a beta y) : ∀ z, y = succ z → PC s a beta z := by
    induction hy with
    | zero =>
      intro z hz
      exact False.elim (not_lt_zero z (hz ▸ lt_succ_self z))
    | seed hy =>
      intro z hz
      exact .seed (lt_trans _ _ _ (lt_succ_self z) (hz ▸ hy))
    | @add u v hu hv ihu ihv =>
      intro z hz
      classical
      by_cases hv0 : v = 0
      · rw [hv0, add_zero] at hz
        exact ihu z hz
      · obtain ⟨w, hw⟩ := right_is_succ_of_add_succ u v z hv0 hz
        have hsum := PC.add hu (ihv w hw)
        rw [hw, add_succ] at hz
        exact (succ_injective hz) ▸ hsum
    | @index r b hr hb ihr ihb =>
      intro z hz
      have hp := I_addPrincipal s r b
      rw [hz] at hp
      rw [addPrincipal_succ_pred_zero z hp]
      exact .zero
    | @collapse k b hb hk hkc hbc ihk ihb =>
      intro z hz
      have hp := psi_addPrincipal s k b (regularIndex_regular s k hk.1)
      rw [hz] at hp
      rw [addPrincipal_succ_pred_zero z hp]
      exact .zero
  exact aux (succ x) hx x rfl

theorem PC_normal_index_parameters (s : Supply) (a beta r b : O)
    (hr : r < I s r b) (hb : b < I s r b) (hx : PC s a beta (I s r b)) :
    PC s a beta r ∧ PC s a beta b := by
  have aux (y : O) (hy : PC s a beta y) :
      ∀ q c, q < I s q c → c < I s q c → y = I s q c → PC s a beta q ∧ PC s a beta c := by
    induction hy with
    | zero =>
      intro q c hq hc heq
      rw [← heq] at hq
      exact False.elim (not_lt_zero _ hq)
    | seed hy =>
      intro q c hq hc heq
      rw [heq] at hy
      exact ⟨.seed (lt_trans _ _ _ hq hy), .seed (lt_trans _ _ _ hc hy)⟩
    | @add u v hu hv ihu ihv =>
      intro q c hq hc heq
      have hup : u ≤ I s q c := heq ▸ le_add u v
      have hvp : v ≤ I s q c := heq ▸ right_le_add u v
      rcases hup with hup | hup
      · rcases hvp with hvp | hvp
        · have hh := I_addPrincipal s q c u v hup hvp
          rw [heq] at hh
          exact False.elim (lt_irrefl _ hh)
        · exact ihv q c hq hc hvp
      · exact ihu q c hq hc hup
    | @index u v hu hv ihu ihv =>
      intro q c hq hc heq
      have hup : u ≤ I s q c := heq ▸ rank_le_I s u v
      have hvp : v ≤ I s q c := heq ▸ index_le_I s u v
      rcases hup with hup | hup
      · rcases hvp with hvp | hvp
        · have he := I_normal_injective s u v q c (heq ▸ hvp) hc heq
          exact ⟨he.1 ▸ hu, he.2 ▸ hv⟩
        · exact ihv q c hq hc hvp
      · exact ihu q c hq hc hup
    | @collapse k c hc hk hkc hcc ihk ihc =>
      intro q d hq hd heq
      exact False.elim (I_normal_ne_psi s q d k c (regularIndex_regular s k hk.1) hq hd heq.symm)
  exact aux (I s r b) hx r b hr hb rfl

theorem PC_I_interval (s : Supply) (cutoff beta r z x : O) (hx : PC s cutoff beta x)
    (hlo : I s r z ≤ x) (hhi : x < I s r (succ z)) : PC s cutoff beta z := by
  induction hx with
  | zero => exact False.elim (lt_irrefl _ (lt_of_lt_of_le (I_pos s r z) hlo))
  | seed hy => exact .seed (lt_of_le_of_lt (le_trans (index_le_I s r z) hlo) hy)
  | @add u w hu hw ihu ihw =>
    by_cases hu' : I s r z ≤ u
    · exact ihu hu' (lt_of_le_of_lt (le_add u w) hhi)
    · have hul : u < I s r z := by
        rcases lt_total u (I s r z) with h | h | h
        · exact h
        · exact False.elim (hu' (Or.inr h.symm))
        · exact False.elim (hu' (Or.inl h))
      apply ihw _ (lt_of_le_of_lt (right_le_add u w) hhi)
      apply (not_lt_iff_le _ _).mp
      intro hwl
      exact (not_lt_iff_le _ _).mpr hlo (I_addPrincipal s r z u w hul hwl)
  | @index u w hu hw ihu ihw =>
    rcases lt_total u r with hur | rfl | hru
    · rw [← I_rank_fixed s u r z hur] at hlo
      rw [← I_rank_fixed s u r (succ z) hur] at hhi
      exact ihw ((I_le_iff s u _ _).mp hlo) ((I_lt_iff s u _ _).mp hhi)
    · have hzw := (I_le_iff s u _ _).mp hlo
      have hwz := (lt_succ_iff_le _ _).mp ((I_lt_iff s u _ _).mp hhi)
      exact (le_antisymm hwz hzw) ▸ hw
    · have hfix := I_rank_fixed s r u w hru
      rw [← hfix] at hlo hhi
      have hzw := (I_le_iff s r _ _).mp hlo
      have hwz := (lt_succ_iff_le _ _).mp ((I_lt_iff s r _ _).mp hhi)
      rw [← le_antisymm hwz hzw]
      exact .index hu hw
  | @collapse k b hb hp hkc hbc ihk ihb =>
    have hk := hp.1
    have hreg := regularIndex_regular s k hk
    rcases lt_total k (I s r (succ z)) with hkl | hkl | hlk
    · rcases lt_total k (I s r z) with hkz | hkz | hzk
      · exact False.elim (lt_asymm (lt_of_le_of_lt hlo (psi_lt s k b hreg)) hkz)
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo (hkz ▸ psi_lt s k b hreg)))
      · exact ihk (Or.inl hzk) hkl
    · rw [hkl] at hkc
      exact PC_predecessor s cutoff beta z
        (PC_normal_index_parameters s cutoff beta r (succ z) (rank_lt_I_succ s r z) (succ_lt_I s r z) hkc).2
    · have hlim := psi_isLimit_of_ge s k b r z hk hlo
      by_cases hzx : z < psi s k b
      · by_cases hrx : r < psi s k b
        · have hmem := C_index s b (psi s k b) r (succ z) (C_seed s b _ r hrx)
            (C_seed s b _ (succ z) (succ_lt_limit hlim hzx))
          exact False.elim (lt_asymm hhi (psi_closed s k b _ hmem hlk))
        · have hxr : psi s k b ≤ r := (not_lt_iff_le _ _).mp hrx
          have h1 : I s r z ≤ I s r 0 := le_trans hlo (le_trans hxr (rank_le_I s r 0))
          rw [le_antisymm ((I_le_iff s r _ _).mp h1) (zero_le z)]
          exact .zero
      · have hxz : psi s k b ≤ z := (not_lt_iff_le _ _).mp hzx
        rw [le_antisymm (le_trans (index_le_I s r z) hlo) hxz]
        exact .collapse hb hp hkc hbc

end
end OCF.Denis
