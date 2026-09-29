import Multi.term3.Denis.NestedNormalization

/-! Recover the canonical parameters of a successor-rank collapse from
its value in a closure. This does not assert hereditary closure of the
index displayed by an arbitrary, equivalent collapse presentation. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem successor_rank_zero_fixedpoint (s : Supply) (r : O) (hr : RankBounded s r) :
    I s r (psi s (I s (succ r) 0) 0) = psi s (I s (succ r) 0) 0 := by
  rw [← (bounded_rank_zero_fundamentalSequence s r hr).sup_eq]
  exact indexIter_sup_fixedpoint s r

theorem first_lt_successor_rank_zero (s : Supply) (r : O) (hr : RankBounded s r) :
    I s 0 0 < psi s (I s (succ r) 0) 0 := by
  have h := (bounded_rank_zero_fundamentalSequence s r hr).below 1
  change I s r 0 < _ at h
  have hmono := first_rank_mono s (zero_le r)
  rw [← I_zero, ← I_zero] at hmono
  exact lt_of_le_of_lt hmono h

/-- Every closure value between the canonical zero collapse and its
index carries the rank parameter. The cutoff and seed are arbitrary. -/
theorem C_successor_rank_interval (s : Supply) (r cutoff beta x : O)
    (hr : RankBounded s r) (hx : C s cutoff beta x)
    (hlower : psi s (I s (succ r) 0) 0 ≤ x) (hupper : x ≤ I s (succ r) 0) :
    C s cutoff beta r := by
  let p := psi s (I s (succ r) 0) 0
  let l := I s (succ r) 0
  have hreg : RegularIndex s l := Or.inl ⟨succ r, rfl⟩
  have hrp : r < p := rank_lt_psi_first_succ_rank s r hr
  have hsp : succ r < p := succ_lt_limit (bounded_rank_zero_fundamentalSequence s r hr).isLimit hrp
  have hp : AddPrincipal p := psi_addPrincipal s l 0 (regularIndex_regular s l hreg)
  have hfix : I s r p = p := successor_rank_zero_fixedpoint s r hr
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
      · have hsmall := I_lower_rank_closed s q r p b hqr (hfix.symm ▸ hbp)
        rw [hfix] at hsmall
        exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlower hsmall))
      · exact ihb (Or.inr hbp.symm) (le_trans (index_le_I s q b) hupper)
      · exact ihb (Or.inl hpb) (le_trans (index_le_I s q b) hupper)
    · exact hqr ▸ (C_iff s cutoff beta q).mpr hq
    · have hsq : succ r ≤ q := (succ_le_iff_lt r q).mpr hrq
      rcases hsq with hsq | hsq
      · have hlarge := first_rank_strict s hsq
        rw [← I_zero, ← I_zero] at hlarge
        exact False.elim (lt_irrefl _ (lt_of_lt_of_le hlarge
          (le_trans (I_mono s q (zero_le b)) hupper)))
      · apply C_predecessor s cutoff beta r
        exact hsq.symm ▸ (C_iff s cutoff beta q).mpr hq
  | @collapse k a ha hk hkc hac ihk iha =>
    change p ≤ psi s k a at hlower
    change psi s k a ≤ l at hupper
    rcases lt_total k l with hkl | hkl | hlk
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k a (regularIndex_regular s k hk)))) (Or.inl hkl)
    · exact ihk (Or.inl (lt_of_le_of_lt hlower (psi_lt s k a (regularIndex_regular s k hk)))) (Or.inr hkl)
    · have hlC : C s a (psi s k a) l := C_index s a _ (succ r) 0
        (C_seed s a _ _ (lt_of_lt_of_le hsp hlower)) (C_zero s a _)
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le (psi_closed s k a l hlC hlk) hupper))

theorem successor_rank_index_mem_argument (s : Supply) (r a : O) (hr : RankBounded s r) :
    C s a (psi s (I s (succ r) 0) a) (I s (succ r) 0) :=
  C_mono_seed s a _ _ (psi_mono s _ 0 a (zero_le a)) _
    (C_mono_argument s 0 a _ (zero_le a) _ (successor_rank_index_mem s r hr))

theorem successor_rank_small_argument_mem (s : Supply) (r a : O) (hr : RankBounded s r)
    (ha : a < I s 0 0) :
    C s a (psi s (I s (succ r) 0) a) (I s (succ r) 0) ∧
      C s a (psi s (I s (succ r) 0) a) a := by
  have hmono := psi_mono s (I s (succ r) 0) 0 a (zero_le a)
  refine ⟨successor_rank_index_mem_argument s r a hr, ?_⟩
  exact C_seed s a _ a (lt_of_lt_of_le
    (lt_trans _ _ _ ha (first_lt_successor_rank_zero s r hr)) hmono)

/-- A value with canonical successor-rank index and admissible argument
below that index
forces the same argument in every regular-index collapse presentation. -/
theorem successor_rank_below_presentation (s : Supply) (r a k b : O)
    (hr : RankBounded s r) (ha : a < I s (succ r) 0)
    (haC : C s a (psi s (I s (succ r) 0) a) a) (hk : RegularIndex s k)
    (heq : psi s k b = psi s (I s (succ r) 0) a) :
    k ≤ I s (succ r) 0 ∧ b = a := by
  let l := I s (succ r) 0
  have hl : RegularIndex s l := Or.inl ⟨succ r, rfl⟩
  have hmono := psi_mono s l 0 a (zero_le a)
  have hsp : succ r < psi s l a := lt_of_lt_of_le
    (succ_lt_limit (bounded_rank_zero_fundamentalSequence s r hr).isLimit
      (rank_lt_psi_first_succ_rank s r hr)) hmono
  have hkl : k ≤ l := by
    apply (not_lt_iff_le l k).mp
    intro hlk
    have hlC := C_index s b (psi s k b) (succ r) 0
      (C_seed s b _ _ (heq.symm ▸ hsp)) (C_zero s b _)
    have h := psi_closed s k b l hlC hlk
    rw [heq] at h
    exact lt_asymm h (psi_lt s l a (regularIndex_regular s l hl))
  refine ⟨hkl, ?_⟩
  rcases lt_total b a with hba | hba | hab
  · have hlC := successor_rank_index_mem_argument s r b hr
    have hbC := C_seed s b (psi s l b) b (psi_argument_normal_below s l a b ha haC hba)
    have hstrict := psi_strict_of_mem s l b a hl hba hlC hbC
    have h := lt_of_le_of_lt (psi_mono_index s k l b hkl) hstrict
    rw [heq] at h
    exact False.elim (lt_irrefl _ h)
  · exact hba
  · exact False.elim (psi_ne_of_argument_lt s l a k b hl hk hab
      (successor_rank_index_mem_argument s r a hr) haC heq.symm)

theorem successor_rank_small_presentation (s : Supply) (r a k b : O)
    (hr : RankBounded s r) (ha : a < I s 0 0) (hk : RegularIndex s k)
    (heq : psi s k b = psi s (I s (succ r) 0) a) :
    k ≤ I s (succ r) 0 ∧ b = a :=
  successor_rank_below_presentation s r a k b hr
    (lt_of_lt_of_le ha (I_lower_bound s (succ r) 0))
    (successor_rank_small_argument_mem s r a hr ha).2 hk heq

/-- Recover the admissible argument below the index from closure membership of the value,
even when that value was constructed using a different collapse index. -/
theorem C_successor_rank_below_argument (s : Supply) (r a cutoff beta : O)
    (hr : RankBounded s r) (ha : a < I s (succ r) 0)
    (haC : C s a (psi s (I s (succ r) 0) a) a)
    (hx : C s cutoff beta (psi s (I s (succ r) 0) a)) : C s cutoff beta a := by
  let l := I s (succ r) 0
  have hl : RegularIndex s l := Or.inl ⟨succ r, rfl⟩
  have hsmall : a < psi s l a := psi_closed s l a a haC ha
  have hp := psi_addPrincipal s l a (regularIndex_regular s l hl)
  have aux (y : O) (hy : C s cutoff beta y) : y = psi s l a → C s cutoff beta a := by
    have h := (C_iff s cutoff beta y).mp hy
    clear hy
    induction h with
    | zero =>
      intro heq
      exact False.elim (not_lt_zero a (heq.symm ▸ hsmall))
    | seed hy =>
      intro heq
      exact C_seed s cutoff beta a (lt_trans _ _ _ hsmall (heq ▸ hy))
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
      have hba := (successor_rank_below_presentation s r a k b hr ha haC hk heq).2
      exact hba ▸ (C_iff s cutoff beta b).mpr hbc
  exact aux _ hx rfl

theorem C_successor_rank_small_argument (s : Supply) (r a cutoff beta : O)
    (hr : RankBounded s r) (ha : a < I s 0 0)
    (hx : C s cutoff beta (psi s (I s (succ r) 0) a)) : C s cutoff beta a :=
  C_successor_rank_below_argument s r a cutoff beta hr
    (lt_of_lt_of_le ha (I_lower_bound s (succ r) 0))
    (successor_rank_small_argument_mem s r a hr ha).2 hx

theorem C_successor_rank_below_parameters (s : Supply) (r a cutoff beta : O)
    (hr : RankBounded s r) (ha : a < I s (succ r) 0)
    (haC : C s a (psi s (I s (succ r) 0) a) a)
    (hx : C s cutoff beta (psi s (I s (succ r) 0) a)) :
    C s cutoff beta r ∧ C s cutoff beta a :=
  ⟨C_successor_rank_interval s r cutoff beta _ hr hx
      (psi_mono s _ 0 a (zero_le a)) (psi_le s _ a),
    C_successor_rank_below_argument s r a cutoff beta hr ha haC hx⟩

theorem C_successor_rank_small_parameters (s : Supply) (r a cutoff beta : O)
    (hr : RankBounded s r) (ha : a < I s 0 0)
    (hx : C s cutoff beta (psi s (I s (succ r) 0) a)) :
    C s cutoff beta r ∧ C s cutoff beta a :=
  ⟨C_successor_rank_interval s r cutoff beta _ hr hx
      (psi_mono s _ 0 a (zero_le a)) (psi_le s _ a),
    C_successor_rank_small_argument s r a cutoff beta hr ha hx⟩

end
end OCF.Denis
