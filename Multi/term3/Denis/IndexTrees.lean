import Multi.term3.Denis.CountableRegular

/-! Closure approximation for normal I/add expressions with countable
leaves. Parameters may be uncountable and may contain arbitrarily many
nested I constructors. Uncountable collapse leaves are not included. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem principal_eq_of_below_repeat {p x : O} (hx : AddPrincipal x)
    (hpx : p ≤ x) (n : Nat) (hxp : x < repeatAdd p n) : x = p := by
  rcases hpx with hpx | hpx
  · have hb : ∀ m, repeatAdd p m < x := by
      intro m
      induction m with
      | zero => exact lt_of_le_of_lt (zero_le p) hpx
      | succ m ih => exact hx p _ hpx ih
    exact False.elim (lt_asymm hxp (hb n))
  · exact hpx.symm

theorem C_principal_head_below_repeat (s : Supply) (a beta p x : O) (hp : AddPrincipal p)
    (hx : C s a beta x) (hpx : p ≤ x) (n : Nat) (hxp : x < repeatAdd p n) : C s a beta p := by
  have h := (C_iff s a beta x).mp hx
  clear hx
  induction h with
  | zero =>
    rw [le_antisymm hpx (zero_le p)]
    exact C_zero s a beta
  | seed hx => exact C_seed s a beta p (lt_of_le_of_lt hpx hx)
  | @add u v hu hv ihu ihv =>
    rcases lt_total u p with hup | hup | hpu
    · rcases lt_total v p with hvp | hvp | hpv
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hpx (hp u v hup hvp)))
      · exact ihv (Or.inr hvp.symm) (lt_of_le_of_lt (right_le_add u v) hxp)
      · exact ihv (Or.inl hpv) (lt_of_le_of_lt (right_le_add u v) hxp)
    · exact ihu (Or.inr hup.symm) (lt_of_le_of_lt (le_add u v) hxp)
    · exact ihu (Or.inl hpu) (lt_of_le_of_lt (le_add u v) hxp)
  | @index q c hq hc ihq ihc =>
    have heq := principal_eq_of_below_repeat (I_addPrincipal s q c) hpx n hxp
    exact heq ▸ C_index s a beta q c ((C_iff s a beta q).mpr hq) ((C_iff s a beta c).mpr hc)
  | @collapse k c hc hk hkc hcc ihk ihc =>
    change p ≤ psi s k c at hpx
    change psi s k c < repeatAdd p n at hxp
    have heq := principal_eq_of_below_repeat (psi_addPrincipal s k c (regularIndex_regular s k hk)) hpx n hxp
    exact heq ▸ C_collapse s a beta k c hc hk ((C_iff s a beta k).mpr hkc) ((C_iff s a beta c).mpr hcc)

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem C_normal_sum_components (s : OCF.Denis.Supply) (cutoff beta : OCF.Denis.O)
    (a b : Term) (ht : IsNormal s (.add a b)) (hC : OCF.Denis.C s cutoff beta (denote s (.add a b))) :
    OCF.Denis.C s cutoff beta (denote s a) ∧ OCF.Denis.C s cutoff beta (denote s b) := by
  have hn := normal_lt_repeat_leading s (.add a b) ht (by intro h; cases h)
  cases ht with
  | sum ha hb hap hp hbpos hhead =>
    obtain ⟨n, hn⟩ := hn
    change denote s a + denote s b < OCF.Denis.repeatAdd (denote s a.leading) n at hn
    rw [leading_eq_of_principal a hap] at hn
    exact ⟨OCF.Denis.C_principal_head_below_repeat s cutoff beta (denote s a) _ hp hC
        (le_add _ _) n hn,
      OCF.Denis.C_suffix s cutoff beta _ (denote s a) (denote s b) hC rfl⟩

def NormalApproximation (s : OCF.Denis.Supply) (r x : OCF.Denis.O) : Prop :=
  ∃ c, Represented s c ∧ c < r ∧ OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) c ∧
    OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) x

theorem normalApproximation_pair (s : OCF.Denis.Supply) (r x y : OCF.Denis.O)
    (hx : NormalApproximation s r x) (hy : NormalApproximation s r y) :
    ∃ c, Represented s c ∧ c < r ∧ OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) c ∧
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) x ∧
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) y := by
  obtain ⟨c, hc, hcr, hcc, hcx⟩ := hx
  obtain ⟨d, hd, hdr, hdd, hdy⟩ := hy
  have promote (a b z : OCF.Denis.O) (hab : a ≤ b)
      (hz : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) z) :
      OCF.Denis.C s b (OCF.Denis.psi s (OCF.Denis.I s 0 0) b) z :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ _ _ hab) z
      (OCF.Denis.C_mono_argument s _ _ _ hab z hz)
  rcases OCF.Ordinal.lt_total c d with h | h | h
  · exact ⟨d, hd, hdr, hdd, promote c d x (Or.inl h) hcx, hdy⟩
  · exact ⟨d, hd, hdr, hdd, h ▸ hcx, hdy⟩
  · exact ⟨c, hc, hcr, hcc, hcx, promote d c y (Or.inl h) hdy⟩

/-- A normal expression whose uncountable part uses I and addition.
Countable normal expressions, including collapses, may occur as leaves. -/
inductive IndexTree (s : OCF.Denis.Supply) : Term → Prop where
  | small {t : Term} : IsNormal s t → denote s t < OCF.Denis.I s 0 0 → IndexTree s t
  | index {r b : Term} : IndexTree s r → IndexTree s b → IsNormal s (.I r b) → IndexTree s (.I r b)
  | sum {a b : Term} : IndexTree s a → IndexTree s b → IsNormal s (.add a b) → IndexTree s (.add a b)

theorem IndexTree.normal {s : OCF.Denis.Supply} {t : Term} (ht : IndexTree s t) : IsNormal s t := by
  cases ht with
  | small ht _ | index _ _ ht | sum _ _ ht => exact ht

theorem IndexTree.approximation {s : OCF.Denis.Supply} {t : Term} (ht : IndexTree s t)
    (r : OCF.Denis.O) (hr : OCF.Denis.UncountableRegular r)
    (hC : OCF.Denis.C s r (OCF.Denis.psi s (OCF.Denis.I s 0 0) r) (denote s t)) :
    NormalApproximation s r (denote s t) := by
  induction ht with
  | @small t ht hsmall =>
    have hlt := OCF.Denis.psi_closed s _ _ _ hC hsmall
    obtain ⟨c, hc, hcr, htc, hcc⟩ := normal_interpolation s r hr t ht hlt
    exact ⟨c, hc, hcr, hcc, OCF.Denis.C_seed s _ _ _ htc⟩
  | @index p b hp hb ht ihp ihb =>
    cases ht with
    | index hpn hbn hpl hbl =>
      obtain ⟨hpC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ (denote s p) (denote s b) hpl hbl hC
      obtain ⟨c, hc, hcr, hcc, hcp, hcb⟩ := normalApproximation_pair s r _ _ (ihp hpC) (ihb hbC)
      exact ⟨c, hc, hcr, hcc, OCF.Denis.C_index s _ _ _ _ hcp hcb⟩
  | @sum a b ha hb ht iha ihb =>
    obtain ⟨haC, hbC⟩ := C_normal_sum_components s _ _ a b ht hC
    obtain ⟨c, hc, hcr, hcc, hca, hcb⟩ := normalApproximation_pair s r _ _ (iha haC) (ihb hbC)
    exact ⟨c, hc, hcr, hcc, OCF.Denis.C_add s _ _ _ _ hca hcb⟩

theorem indexTree_diagonal_dense (s : OCF.Denis.Supply) (t : Term) (ht : IndexTree s t)
    (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) := by
  rcases OCF.Denis.regularIndex_lower_bound s _ hreg with hlarge | heq
  · obtain ⟨c, hc, hcr, hcc, hct⟩ := ht.approximation _ (OCF.Denis.regularIndex_regular s _ hreg) harg
    exact seeded_diagonal_dense s _ c ⟨t, ht.normal, rfl⟩ hc hreg hlarge ⟨hcr, hcc, hct⟩
  · rw [← heq]
    exact epsilon_dense s

theorem revised_indexTree_diagonal_fundamentalSequence (s : OCF.Denis.Supply)
    (t : Term) (ht : IndexTree s t) (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (indexTree_diagonal_dense s t ht hreg harg)

end
end T.Correspondence.Denis.Covering
