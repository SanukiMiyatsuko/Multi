import Multi.term3.Denis.FirstInterval

/-! Closure under predecessors and elimination of a redundant collapse
argument. These allow the normal successor branch at the first regular
index to be handled without a bound on its argument. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem C_predecessor (s : Supply) (a beta x : O) (hx : C s a beta (succ x)) :
    C s a beta x := by
  have aux (y : O) (hy : C s a beta y) : ∀ z, y = succ z → C s a beta z := by
    have h := (C_iff s a beta y).mp hy
    clear hy
    induction h with
    | zero =>
      intro z hz
      exact False.elim (not_lt_zero z (hz ▸ lt_succ_self z))
    | seed hy =>
      intro z hz
      exact C_seed s a beta z (lt_trans _ _ _ (lt_succ_self z) (hz ▸ hy))
    | @add u v hu hv ihu ihv =>
      intro z hz
      classical
      by_cases hv0 : v = 0
      · rw [hv0, add_zero] at hz
        exact ihu z hz
      · obtain ⟨w, hw⟩ := right_is_succ_of_add_succ u v z hv0 hz
        have hwC := ihv w hw
        have hsum : C s a beta (u + w) :=
          C_add s a beta u w ((C_iff s a beta u).mpr hu) hwC
        rw [hw, add_succ] at hz
        exact (succ_injective hz) ▸ hsum
    | @index r b hr hb ihr ihb =>
      intro z hz
      have hp := I_addPrincipal s r b
      rw [hz] at hp
      rw [addPrincipal_succ_pred_zero z hp]
      exact C_zero s a beta
    | @collapse k b hb hk hc hd ihc ihd =>
      intro z hz
      change psi s k b = succ z at hz
      have hp := psi_addPrincipal s k b (regularIndex_regular s k hk)
      rw [hz] at hp
      rw [addPrincipal_succ_pred_zero z hp]
      exact C_zero s a beta
  exact aux (succ x) hx x rfl

theorem addPrincipal_suffix {p r b : O} (hp : AddPrincipal p) (heq : p = r + b) :
    b = 0 ∨ b = p := by
  have hbp : b ≤ p := heq ▸ right_le_add r b
  rcases hbp with hbp | hbp
  · have hrp : r ≤ p := heq ▸ le_add r b
    rcases hrp with hrp | hrp
    · have h := hp r b hrp hbp
      rw [← heq] at h
      exact False.elim (lt_irrefl _ h)
    · rw [hrp] at heq
      exact Or.inl (add_right_cancel (heq.symm.trans (add_zero p).symm))
  · exact Or.inr hbp

/-- Every ordinal suffix of a closure element is again in the closure. -/
theorem C_suffix (s : Supply) (a beta x r b : O) (hx : C s a beta x) (heq : x = r + b) :
    C s a beta b := by
  have aux (y : O) (hy : C s a beta y) : ∀ u v, y = u + v → C s a beta v := by
    have h := (C_iff s a beta y).mp hy
    clear hy
    induction h with
    | zero =>
      intro u v hv
      have hvle : v ≤ (0 : O) := hv ▸ right_le_add u v
      rw [le_antisymm hvle (zero_le v)]
      exact C_zero s a beta
    | seed hy =>
      intro u v hv
      have hvle : v ≤ _ := hv ▸ right_le_add u v
      exact C_seed s a beta v (lt_of_le_of_lt hvle hy)
    | @add u v hu hv ihu ihv =>
      intro q t heq
      rcases lt_total q u with hqu | hqu | huq
      · obtain ⟨c, hc⟩ := exists_add_of_le q u (Or.inl hqu)
        have hcC := ihu q c hc
        have hsum := C_add s a beta c v hcC ((C_iff s a beta v).mpr hv)
        rw [hc, add_assoc] at heq
        exact (add_right_cancel heq) ▸ hsum
      · rw [hqu] at heq
        exact (add_right_cancel heq) ▸ (C_iff s a beta v).mpr hv
      · obtain ⟨c, hc⟩ := exists_add_of_le u q (Or.inl huq)
        rw [hc, add_assoc] at heq
        exact ihv c t (add_right_cancel heq)
    | @index q c hq hc ihq ihc =>
      intro u v hv
      rcases addPrincipal_suffix (I_addPrincipal s q c) hv with hz | hz
      · rw [hz]; exact C_zero s a beta
      · rw [hz]
        exact C_index s a beta q c ((C_iff s a beta q).mpr hq) ((C_iff s a beta c).mpr hc)
    | @collapse k c hc hk hkc hcc ihk ihc =>
      intro u v hv
      change psi s k c = u + v at hv
      rcases addPrincipal_suffix (psi_addPrincipal s k c (regularIndex_regular s k hk)) hv with hz | hz
      · rw [hz]; exact C_zero s a beta
      · rw [hz]
        exact C_collapse s a beta k c hc hk ((C_iff s a beta k).mpr hkc) ((C_iff s a beta c).mpr hcc)
  exact aux x hx r b heq

/-- Normal I parameters are recoverable even from a different closure
expression denoting the same index. -/
theorem C_normal_index_parameters (s : Supply) (a beta r b : O)
    (hr : r < I s r b) (hb : b < I s r b) (hx : C s a beta (I s r b)) :
    C s a beta r ∧ C s a beta b := by
  have aux (y : O) (hy : C s a beta y) :
      ∀ q c, q < I s q c → c < I s q c → y = I s q c → C s a beta q ∧ C s a beta c := by
    have h := (C_iff s a beta y).mp hy
    clear hy
    induction h with
    | zero =>
      intro q c hq hc heq
      rw [← heq] at hq
      exact False.elim (not_lt_zero _ hq)
    | seed hy =>
      intro q c hq hc heq
      rw [heq] at hy
      exact ⟨C_seed s a beta q (lt_trans _ _ _ hq hy), C_seed s a beta c (lt_trans _ _ _ hc hy)⟩
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
          exact ⟨he.1 ▸ (C_iff s a beta u).mpr hu, he.2 ▸ (C_iff s a beta v).mpr hv⟩
        · exact ihv q c hq hc hvp
      · exact ihu q c hq hc hup
    | @collapse k c hc hk hkc hcc ihk ihc =>
      intro q d hq hd heq
      change psi s k c = I s q d at heq
      exact False.elim (I_normal_ne_psi s q d k c (regularIndex_regular s k hk) hq hd heq.symm)
  exact aux (I s r b) hx r b hr hb rfl

theorem principal_eq_of_between_double {p x : O} (hx : AddPrincipal x)
    (hpx : p ≤ x) (hxp : x < p + p) : x = p := by
  rcases hpx with hpx | hpx
  · exact False.elim (lt_asymm hxp (hx p p hpx hpx))
  · exact hpx.symm

theorem C_principal_head (s : Supply) (a beta p x : O) (hp : AddPrincipal p)
    (hx : C s a beta x) (hpx : p ≤ x) (hxp : x < p + p) : C s a beta p := by
  have h := (C_iff s a beta x).mp hx
  clear hx
  induction h with
  | zero =>
    rw [le_antisymm hpx (zero_le p)]
    exact C_zero s a beta
  | seed hx => exact C_seed s a beta p (lt_of_le_of_lt hpx hx)
  | @add u v hu hv ihu ihv =>
    classical
    by_cases hpu : p ≤ u
    · exact ihu hpu (lt_of_le_of_lt (le_add u v) hxp)
    by_cases hpv : p ≤ v
    · exact ihv hpv (lt_of_le_of_lt (right_le_add u v) hxp)
    have hup : u < p := by
      rcases lt_total u p with hh | hh | hh
      · exact hh
      · exact False.elim (hpu (Or.inr hh.symm))
      · exact False.elim (hpu (Or.inl hh))
    have hvp : v < p := by
      rcases lt_total v p with hh | hh | hh
      · exact hh
      · exact False.elim (hpv (Or.inr hh.symm))
      · exact False.elim (hpv (Or.inl hh))
    exact False.elim (lt_irrefl _ (lt_of_le_of_lt hpx (hp u v hup hvp)))
  | @index q c hq hc ihq ihc =>
    have heq := principal_eq_of_between_double (I_addPrincipal s q c) hpx hxp
    exact heq ▸ C_index s a beta q c ((C_iff s a beta q).mpr hq) ((C_iff s a beta c).mpr hc)
  | @collapse k c hc hk hkc hcc ihk ihc =>
    change p ≤ psi s k c at hpx
    change psi s k c < p + p at hxp
    have heq := principal_eq_of_between_double (psi_addPrincipal s k c (regularIndex_regular s k hk)) hpx hxp
    exact heq ▸ C_collapse s a beta k c hc hk ((C_iff s a beta k).mpr hkc) ((C_iff s a beta c).mpr hcc)

theorem C_principal_prefix (s : Supply) (a beta p b : O) (hp : AddPrincipal p)
    (hb : b < p) (hx : C s a beta (p + b)) : C s a beta p :=
  C_principal_head s a beta p (p + b) hp hx (le_add p b) (add_lt_add_right p hb)

theorem C_successor_of_argument_not_mem (s : Supply) (a beta : O)
    (ha : ¬ C s a beta a) (x : O) (hx : C s (succ a) beta x) : C s a beta x := by
  apply C_least s (succ a) beta (C s a beta) _ _ _ _ _ x hx
  · exact C_zero s a beta
  · exact fun x hx => C_seed s a beta x hx
  · exact fun x y hx hy => C_add s a beta x y hx hy
  · exact fun x y hx hy => C_index s a beta x y hx hy
  · intro k b hb hk hc hd
    rcases (lt_succ_iff_le b a).mp hb with hb | heq
    · exact C_collapse s a beta k b hb hk hc hd
    · rw [heq] at hd
      exact False.elim (ha hd)

theorem psi_successor_eq_of_argument_not_mem (s : Supply) (k a : O)
    (ha : ¬ C s a (psi s k a) a) : psi s k (succ a) = psi s k a := by
  apply le_antisymm _ (psi_mono s k a (succ a) (Or.inl (lt_succ_self a)))
  exact psi_min s k (succ a) (psi s k a) ⟨psi_le s k a,
    fun x hx hxk => psi_closed s k a x (C_successor_of_argument_not_mem s a _ ha x hx) hxk⟩

/-- Parent admissibility alone suffices, including uncountable arguments. -/
theorem psi_predecessor_argument_normal_general (s : Supply) (k a : O)
    (ha : C s (succ a) (psi s k (succ a)) (succ a)) : C s a (psi s k a) a := by
  apply Classical.byContradiction
  intro hn
  rw [psi_successor_eq_of_argument_not_mem s k a hn] at ha
  exact hn (C_predecessor s a (psi s k a) a
    (C_successor_of_argument_not_mem s a _ hn (succ a) ha))

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem psi_first_normal_successor_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a)) (succ a)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a)) :=
  psi_first_successor_dense s a (represented_predecessor s a ha)
    (OCF.Denis.psi_predecessor_argument_normal_general s _ a harg)

/-- Every normal first-index collapse with a successor argument has a
valid repaired sequence; no countability bound on the argument remains. -/
theorem revised_psi_first_normal_successor_general (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a)) (succ a)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (succ a))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (psi_first_normal_successor_dense s a ha harg)

end
end T.Correspondence.Denis.Covering
