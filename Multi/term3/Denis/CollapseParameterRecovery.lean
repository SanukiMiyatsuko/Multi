import Multi.term3.Denis.SuccessorRankClosure

/-! Recover an argument below its proper collapse index from any closure
presentation of its value. For first indices, also recover the rank,
without restricting it to a successor. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_presentation_of_parameters_lt (s : Supply) (r v a k b : O)
    (hl : RegularIndex s (I s r v)) (hk : RegularIndex s k)
    (hr : r < psi s (I s r v) a) (hv : v < psi s (I s r v) a)
    (ha : a < psi s (I s r v) a)
    (heq : psi s k b = psi s (I s r v) a) : k ≤ I s r v ∧ b = a := by
  let l := I s r v
  let p := psi s l a
  have hindex (c : O) : C s c p l :=
    C_index s c p r v (C_seed s c p r hr) (C_seed s c p v hv)
  have hkl : k ≤ l := by
    apply (not_lt_iff_le l k).mp
    intro hlk
    have h := psi_closed s k b l (heq.symm ▸ hindex b) hlk
    rw [heq] at h
    exact lt_asymm h (psi_lt s l a (regularIndex_regular s l hl))
  refine ⟨hkl, ?_⟩
  rcases lt_total b a with hba | hba | hab
  · have hsame : psi s l b = p := le_antisymm (psi_mono s l b a (Or.inl hba))
      (by
        change psi s (I s r v) a ≤ psi s l b
        rw [← heq]
        exact psi_mono_index s k l b hkl)
    have harg : C s b (psi s l b) b := C_seed s b _ b (hsame.symm ▸ lt_trans _ _ _ hba ha)
    have hstrict := psi_strict_of_mem s l b a hl hba (hsame.symm ▸ hindex b) harg
    rw [hsame] at hstrict
    exact False.elim (lt_irrefl _ hstrict)
  · exact hba
  · exact False.elim (psi_ne_of_argument_lt s l a k b hl hk hab (hindex a)
      (C_seed s a p a ha) heq.symm)

theorem C_collapse_argument_of_parameters_lt (s : Supply) (r v a cutoff beta : O)
    (hl : RegularIndex s (I s r v))
    (hr : r < psi s (I s r v) a) (hv : v < psi s (I s r v) a)
    (ha : a < psi s (I s r v) a)
    (hx : C s cutoff beta (psi s (I s r v) a)) : C s cutoff beta a := by
  let l := I s r v
  have hp := psi_addPrincipal s l a (regularIndex_regular s l hl)
  have aux (y : O) (hy : C s cutoff beta y) : y = psi s l a → C s cutoff beta a := by
    have h := (C_iff s cutoff beta y).mp hy
    clear hy
    induction h with
    | zero =>
      intro heq
      exact False.elim (not_lt_zero a (heq.symm ▸ ha))
    | seed hy =>
      intro heq
      exact C_seed s cutoff beta a (lt_trans _ _ _ ha (heq ▸ hy))
    | @add u v hu hv ihu ihv =>
      intro heq
      rcases addPrincipal_suffix hp heq.symm with hv0 | hveq
      · rw [hv0, add_zero] at heq
        exact ihu heq
      · exact ihv hveq
    | @index q b hq hb ihq ihb =>
      intro heq
      rcases rank_le_I s q b with hqr | hqr
      · rcases index_le_I s q b with hbr | hbr
        · exact False.elim (I_normal_ne_psi s q b l a (regularIndex_regular s l hl) hqr hbr heq)
        · exact ihb (hbr.trans heq)
      · exact ihq (hqr.trans heq)
    | @collapse k b hb hk hkc hbc ihk ihb =>
      intro heq
      change psi s k b = psi s l a at heq
      exact (psi_presentation_of_parameters_lt s r v a k b hl hk hr hv ha heq).2 ▸
        (C_iff s cutoff beta b).mpr hbc
  exact aux _ hx rfl

/-- This applies to any proper, normal I-index presentation with argument
below the index, including successor indices and limit ranks. -/
theorem C_proper_collapse_argument_below (s : Supply) (r v a cutoff beta : O)
    (hl : RegularIndex s (I s r v)) (hr : r < I s r v) (hv : v < I s r v)
    (ha : a < I s r v) (hindex : C s a (psi s (I s r v) a) (I s r v))
    (harg : C s a (psi s (I s r v) a) a)
    (hx : C s cutoff beta (psi s (I s r v) a)) : C s cutoff beta a := by
  obtain ⟨hrC, hvC⟩ := C_normal_index_parameters s _ _ _ _ hr hv hindex
  exact C_collapse_argument_of_parameters_lt s r v a cutoff beta hl
    (psi_closed s _ _ _ hrC hr) (psi_closed s _ _ _ hvC hv) (psi_closed s _ _ _ harg ha) hx

theorem C_collapse_index_parameters_interval (s : Supply) (r v a cutoff beta x : O)
    (hl : RegularIndex s (I s r v))
    (hr : r < psi s (I s r v) a) (hv : v < psi s (I s r v) a)
    (hx : C s cutoff beta x)
    (hlower : psi s (I s r v) a ≤ x) (hupper : x ≤ I s r v) :
    C s cutoff beta r ∧ C s cutoff beta v := by
  classical
  let l := I s r v
  let p := psi s l a
  have hpl : p < l := psi_lt s l a (regularIndex_regular s l hl)
  have hp := psi_addPrincipal s l a (regularIndex_regular s l hl)
  have h := (C_iff s cutoff beta x).mp hx
  clear hx
  induction h with
  | zero => exact False.elim (not_lt_zero r (lt_of_lt_of_le hr hlower))
  | seed hx => exact ⟨C_seed s cutoff beta r (lt_trans _ _ _ (lt_of_lt_of_le hr hlower) hx),
      C_seed s cutoff beta v (lt_trans _ _ _ (lt_of_lt_of_le hv hlower) hx)⟩
  | @add u w hu hw ihu ihw =>
    have huup := le_trans (le_add u w) hupper
    have hwup := le_trans (right_le_add u w) hupper
    rcases lt_total u p with hu | hu | hu
    · rcases lt_total w p with hw | hw | hw
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlower (hp u w hu hw)))
      · exact ihw (Or.inr hw.symm) hwup
      · exact ihw (Or.inl hw) hwup
    · exact ihu (Or.inr hu.symm) huup
    · exact ihu (Or.inl hu) huup
  | @index q b hq hb ihq ihb =>
    have hxC := C_index s cutoff beta q b ((C_iff s cutoff beta q).mpr hq) ((C_iff s cutoff beta b).mpr hb)
    rcases hupper with hlt | heq
    · by_cases hqp : q < p
      · by_cases hbp : b < p
        · have hsmall := psi_closed s l a _ (C_index s a p q b (C_seed s a p q hqp) (C_seed s a p b hbp)) hlt
          exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlower hsmall))
        · exact ihb ((not_lt_iff_le _ _).mp hbp) (le_trans (index_le_I s q b) (Or.inl hlt))
      · exact ihq ((not_lt_iff_le _ _).mp hqp) (le_trans (rank_le_I s q b) (Or.inl hlt))
    · exact C_normal_index_parameters s cutoff beta r v (lt_trans _ _ _ hr hpl) (lt_trans _ _ _ hv hpl)
        (heq ▸ hxC)
  | @collapse k b hb hk hkc hbc ihk ihb =>
    change p ≤ psi s k b at hlower
    change psi s k b ≤ l at hupper
    rcases lt_total k l with hkl | hkl | hlk
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k b (regularIndex_regular s k hk)))) (Or.inl hkl)
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k b (regularIndex_regular s k hk)))) (Or.inr hkl)
    · have hlC : C s b (psi s k b) l := C_index s b _ r v
        (C_seed s b _ r (lt_of_lt_of_le hr hlower)) (C_seed s b _ v (lt_of_lt_of_le hv hlower))
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le (psi_closed s k b l hlC hlk) hupper))

theorem C_proper_collapse_index (s : Supply) (r v a cutoff beta : O)
    (hl : RegularIndex s (I s r v)) (hr : r < I s r v) (hv : v < I s r v)
    (hindex : C s a (psi s (I s r v) a) (I s r v))
    (hx : C s cutoff beta (psi s (I s r v) a)) : C s cutoff beta (I s r v) := by
  obtain ⟨hrC, hvC⟩ := C_normal_index_parameters s _ _ _ _ hr hv hindex
  obtain ⟨hrC', hvC'⟩ := C_collapse_index_parameters_interval s r v a cutoff beta _ hl
    (psi_closed s _ _ _ hrC hr) (psi_closed s _ _ _ hvC hv) hx (le_refl _) (psi_le s _ a)
  exact C_index s cutoff beta r v hrC' hvC'

theorem C_proper_collapse_parameters_below (s : Supply) (r v a cutoff beta : O)
    (hl : RegularIndex s (I s r v)) (hr : r < I s r v) (hv : v < I s r v)
    (ha : a < I s r v) (hindex : C s a (psi s (I s r v) a) (I s r v))
    (harg : C s a (psi s (I s r v) a) a)
    (hx : C s cutoff beta (psi s (I s r v) a)) :
    C s cutoff beta (I s r v) ∧ C s cutoff beta a :=
  ⟨C_proper_collapse_index s r v a cutoff beta hl hr hv hindex hx,
    C_proper_collapse_argument_below s r v a cutoff beta hl hr hv ha hindex harg hx⟩

theorem C_first_rank_interval (s : Supply) (r cutoff beta x : O)
    (hr : RankBounded s r) (hx : C s cutoff beta x)
    (hlower : psi s (I s r 0) 0 ≤ x) (hupper : x ≤ I s r 0) : C s cutoff beta r := by
  let p := psi s (I s r 0) 0
  let l := I s r 0
  have hreg : RegularIndex s l := Or.inl ⟨r, rfl⟩
  have hrp : r < p := rank_lt_psi_of_first_le s r l hr (le_refl _)
  have hp : AddPrincipal p := psi_addPrincipal s l 0 (regularIndex_regular s l hreg)
  have hclosed (q b : O) (hqr : q < r) (hb : b < p) : I s q b < p :=
    psi_closed s l 0 _
      (C_index s 0 p q b (C_seed s 0 p q (lt_trans _ _ _ hqr hrp)) (C_seed s 0 p b hb))
      (I_lower_rank_closed s q r 0 b hqr (lt_trans _ _ _ hb (psi_lt s l 0 (regularIndex_regular s l hreg))))
  have h := (C_iff s cutoff beta x).mp hx
  clear hx
  induction h with
  | zero => exact False.elim (not_lt_zero r (lt_of_lt_of_le hrp hlower))
  | seed hx => exact C_seed s cutoff beta r (lt_trans _ _ _ (lt_of_lt_of_le hrp hlower) hx)
  | @add u v hu hv ihu ihv =>
    have huup := le_trans (le_add u v) hupper
    have hvup := le_trans (right_le_add u v) hupper
    rcases lt_total u p with hu | hu | hu
    · rcases lt_total v p with hv | hv | hv
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlower (hp u v hu hv)))
      · exact ihv (Or.inr hv.symm) hvup
      · exact ihv (Or.inl hv) hvup
    · exact ihu (Or.inr hu.symm) huup
    · exact ihu (Or.inl hu) huup
  | @index q b hq hb ihq ihb =>
    rcases lt_total q r with hqr | hqr | hrq
    · rcases lt_total b p with hbp | hbp | hpb
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlower (hclosed q b hqr hbp)))
      · exact ihb (Or.inr hbp.symm) (le_trans (index_le_I s q b) hupper)
      · exact ihb (Or.inl hpb) (le_trans (index_le_I s q b) hupper)
    · exact hqr ▸ (C_iff s cutoff beta q).mpr hq
    · have hlarge := first_rank_strict s hrq
      rw [← I_zero, ← I_zero] at hlarge
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le hlarge (le_trans (I_mono s q (zero_le b)) hupper)))
  | @collapse k a ha hk hkc hac ihk iha =>
    change p ≤ psi s k a at hlower
    change psi s k a ≤ l at hupper
    rcases lt_total k l with hkl | hkl | hlk
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k a (regularIndex_regular s k hk)))) (Or.inl hkl)
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k a (regularIndex_regular s k hk)))) (Or.inr hkl)
    · have hlC : C s a (psi s k a) l := C_index s a _ r 0
        (C_seed s a _ r (lt_of_lt_of_le hrp hlower)) (C_zero s a _)
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le (psi_closed s k a l hlC hlk) hupper))

theorem C_first_rank_below_parameters (s : Supply) (r a cutoff beta : O)
    (hr : RankBounded s r) (ha : a < I s r 0)
    (harg : C s a (psi s (I s r 0) a) a)
    (hx : C s cutoff beta (psi s (I s r 0) a)) : C s cutoff beta r ∧ C s cutoff beta a := by
  have hreg : RegularIndex s (I s r 0) := Or.inl ⟨r, rfl⟩
  have hrp := lt_of_lt_of_le (rank_lt_psi_of_first_le s r (I s r 0) hr (le_refl _))
    (psi_mono s _ 0 a (zero_le a))
  exact ⟨C_first_rank_interval s r cutoff beta _ hr hx (psi_mono s _ 0 a (zero_le a)) (psi_le s _ a),
    C_collapse_argument_of_parameters_lt s r 0 a cutoff beta hreg hrp
      (psi_pos s _ a (regular_pos (regularIndex_regular s _ hreg))) (psi_closed s _ _ _ harg ha) hx⟩

end
end OCF.Denis
