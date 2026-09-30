import Multi.term3.Denis.TransfiniteTails

/-! Every normal regular index admits a zero-collapse presentation
whose index belongs to its closure. The new index is an I subterm of
the old one, so the reduction terminates even when the ordinal index
increases. The original ordinal functions and normal-form predicate
are unchanged. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_zero_eq_of_collapse_between (s : Supply) (k l a : O)
    (hlo : psi s k 0 ≤ psi s l a) (hhi : psi s l a < k) :
    psi s k 0 = psi s l 0 := by
  rcases lt_total k l with h | h | h
  · exact psi_index_plateau s k l 0
      (le_trans (psi_mono s l 0 a (zero_le a)) (Or.inl hhi)) (Or.inl h)
  · rw [h]
  · exact (psi_index_plateau s l k 0 (le_trans hlo (psi_le s l a)) (Or.inl h)).symm

theorem regular_I_argument (s : Supply) (r b : O) (hb : b < I s r b)
    (hreg : UncountableRegular (I s r b)) : b = 0 ∨ ∃ c, b = succ c := by
  classical
  by_cases hz : b = 0
  · exact Or.inl hz
  by_cases hs : ∃ c, b = succ c
  · exact Or.inr hs
  obtain ⟨d, hd, hfd⟩ := hreg.2 b hb (fun i => I s r (type ((representative b).below i)))
    (fun i => I_strict s r (initial_lt b i))
  have hle : I s r b ≤ d := by
    rw [I_limit s r b hz hs]
    exact (sup_le_iff _ d).mpr (fun i => Or.inl (hfd i))
  exact False.elim (lt_irrefl _ (lt_of_le_of_lt hle hd))

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering.ZeroIndex
open OCF.Ordinal
noncomputable section

inductive Subterm : Term → Term → Prop where
  | refl (a : Term) : Subterm a a
  | addLeft {t a b : Term} : Subterm t a → Subterm t (.add a b)
  | addRight {t a b : Term} : Subterm t b → Subterm t (.add a b)
  | indexRank {t r b : Term} : Subterm t r → Subterm t (.I r b)
  | indexArgument {t r b : Term} : Subterm t b → Subterm t (.I r b)
  | collapseIndex {t k a : Term} : Subterm t k → Subterm t (.psi k a)
  | collapseArgument {t k a : Term} : Subterm t a → Subterm t (.psi k a)

theorem Subterm.trans {a b c : Term} (hab : Subterm a b) (hbc : Subterm b c) : Subterm a c := by
  induction hbc with
  | refl => exact hab
  | addLeft _ ih => exact .addLeft ih
  | addRight _ ih => exact .addRight ih
  | indexRank _ ih => exact .indexRank ih
  | indexArgument _ ih => exact .indexArgument ih
  | collapseIndex _ ih => exact .collapseIndex ih
  | collapseArgument _ ih => exact .collapseArgument ih

theorem Subterm.size_le {a b : Term} (h : Subterm a b) : sizeOf a ≤ sizeOf b := by
  induction h with
  | refl => exact Nat.le_refl _
  | addLeft _ ih | addRight _ ih | indexRank _ ih | indexArgument _ ih | collapseIndex _ ih | collapseArgument _ ih => simp_all; omega

theorem Subterm.index_rank_size_lt {r b k : Term} (h : Subterm (.I r b) k) : sizeOf r < sizeOf k := by
  have hs := h.size_le
  simp at hs
  omega

theorem Subterm.normal {s : OCF.Denis.Supply} {a b : Term} (h : Subterm a b)
    (hb : IsNormal s b) : IsNormal s a := by
  induction h with
  | refl => exact hb
  | addLeft _ ih => cases hb with | sum ha _ _ _ _ _ => exact ih ha
  | addRight _ ih => cases hb with | sum _ hb _ _ _ _ => exact ih hb
  | indexRank _ ih => cases hb with | index hr _ _ _ => exact ih hr
  | indexArgument _ ih => cases hb with | index _ hb _ _ => exact ih hb
  | collapseIndex _ ih => cases hb with | collapse hk _ _ _ => exact ih hk
  | collapseArgument _ ih => cases hb with | collapse _ ha _ _ => exact ih ha

/-- Above a zero-collapse seed but below its index, a normal term must
contain a collapse subterm in the same interval. Addition and I alone
cannot escape the defining closure. -/
theorem collapse_support (s : OCF.Denis.Supply) (k : OCF.Denis.O) (hk : 0 < k)
    (t : Term) (ht : IsNormal s t) (hlo : OCF.Denis.psi s k 0 ≤ denote s t) (hhi : denote s t < k) :
    ∃ l a, Subterm (.psi l a) t ∧ IsNormal s (.psi l a) ∧
      OCF.Denis.psi s k 0 ≤ denote s (.psi l a) ∧ denote s (.psi l a) < k := by
  classical
  induction ht with
  | zero =>
    exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.psi_pos s k 0 hk) hlo))
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    by_cases hul : denote s u < OCF.Denis.psi s k 0
    · by_cases hvl : denote s v < OCF.Denis.psi s k 0
      · exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_le_of_lt hlo
          (OCF.Denis.psi_closed s k 0 _ (OCF.Denis.C_add s 0 _ _ _
            (OCF.Denis.C_seed s 0 _ _ hul) (OCF.Denis.C_seed s 0 _ _ hvl)) hhi)))
      · obtain ⟨l, a, hs, hn, hl, hh⟩ := ihv ((not_lt_iff_le _ _).mp hvl)
          (OCF.Ordinal.lt_of_le_of_lt (right_le_add _ _) hhi)
        exact ⟨l, a, .addRight hs, hn, hl, hh⟩
    · obtain ⟨l, a, hs, hn, hl, hh⟩ := ihu ((not_lt_iff_le _ _).mp hul)
        (OCF.Ordinal.lt_of_le_of_lt (le_add _ _) hhi)
      exact ⟨l, a, .addLeft hs, hn, hl, hh⟩
  | @index r b hr hb hrl hbl ihr ihb =>
    by_cases hrr : denote s r < OCF.Denis.psi s k 0
    · by_cases hbb : denote s b < OCF.Denis.psi s k 0
      · exact False.elim (OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_le_of_lt hlo
          (OCF.Denis.psi_closed s k 0 _ (OCF.Denis.C_index s 0 _ _ _
            (OCF.Denis.C_seed s 0 _ _ hrr) (OCF.Denis.C_seed s 0 _ _ hbb)) hhi)))
      · obtain ⟨l, a, hs, hn, hl, hh⟩ := ihb ((not_lt_iff_le _ _).mp hbb)
          (OCF.Ordinal.lt_trans _ _ _ hbl hhi)
        exact ⟨l, a, .indexArgument hs, hn, hl, hh⟩
    · obtain ⟨l, a, hs, hn, hl, hh⟩ := ihr ((not_lt_iff_le _ _).mp hrr)
        (OCF.Ordinal.lt_trans _ _ _ hrl hhi)
      exact ⟨l, a, .indexRank hs, hn, hl, hh⟩
  | @collapse l a hl ha hreg harg _ _ =>
    exact ⟨l, a, .refl _, .collapse hl ha hreg harg, hlo, hhi⟩

/-- The final I index is literally a subterm, not merely an ordinal
chosen to have the desired value. Thus its parameters are available
to a structural induction on the original normal term. -/
theorem exists_normal_index (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k)) :
    ∃ r b, Subterm (.I r b) k ∧ IsNormal s (.I r b) ∧
      OCF.Denis.RegularIndex s (denote s (.I r b)) ∧
      OCF.Denis.C s 0 (OCF.Denis.psi s (denote s (.I r b)) 0) (denote s (.I r b)) ∧
      OCF.Denis.psi s (denote s k) 0 = OCF.Denis.psi s (denote s (.I r b)) 0 := by
  classical
  induction k using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h k ih =>
    cases hk with
    | zero => exact False.elim (not_lt_zero _ (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ hreg)))
    | @sum u v hu hv hup hp hvpos hhead =>
      have hkp : AddPrincipal (denote s (.add u v)) :=
        fun _ _ hx hy => OCF.Denis.regular_add_closed (OCF.Denis.regularIndex_regular s _ hreg) hx hy
      have huval : denote s u < denote s (.add u v) := by
        simpa only [Denis.denote, add_zero] using add_lt_add_right (denote s u) hvpos
      have hvval := normal_lt_of_leading_lt s v hv _ hkp (OCF.Ordinal.lt_of_le_of_lt hhead huval)
      exact False.elim (OCF.Ordinal.lt_irrefl _ (hkp _ _ huval hvval))
    | @collapse l a hl ha hlreg harg =>
      have hsize : sizeOf l < sizeOf (Term.psi l a) := by simp; omega
      obtain ⟨r, b, hs, hn, hr, hc, heq⟩ := ih l hsize hl hlreg
      refine ⟨r, b, .collapseIndex hs, hn, hr, hc, ?_⟩
      exact (OCF.Denis.psi_index_plateau s _ (denote s l) 0
        (OCF.Denis.psi_mono s _ 0 (denote s a) (zero_le _)) (OCF.Denis.psi_le s _ _)).trans heq
    | @index r b hr hb hrl hbl =>
      by_cases hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (denote s (.I r b)) 0) (denote s (.I r b))
      · exact ⟨r, b, .refl _, .index hr hb hrl hbl, hreg, hmem, rfl⟩
      have hrr : denote s r < OCF.Denis.psi s (denote s (.I r b)) 0 :=
        OCF.Denis.rank_lt_psi_of_first_le s _ _ (normal_rankBounded s r hr)
          (OCF.Denis.I_mono s _ (zero_le _))
      have hbb : OCF.Denis.psi s (denote s (.I r b)) 0 ≤ denote s b := by
        apply (not_lt_iff_le _ _).mp
        intro hbb
        exact hmem (OCF.Denis.C_index s 0 _ _ _ (OCF.Denis.C_seed s 0 _ _ hrr) (OCF.Denis.C_seed s 0 _ _ hbb))
      obtain ⟨l, a, hs, hn, hlo, hhi⟩ := collapse_support s (denote s (.I r b))
        (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ hreg)) b hb hbb hbl
      have hsize : sizeOf l < sizeOf (Term.I r b) := by
        have hh := hs.size_le
        simp at hh ⊢
        omega
      cases hn with
      | collapse hl ha hlreg harg =>
        obtain ⟨q, c, hqc, hqn, hqr, hqC, hqe⟩ := ih l hsize hl hlreg
        refine ⟨q, c, .indexArgument ((hqc.trans (.collapseIndex (.refl l))).trans hs), hqn, hqr, hqC, ?_⟩
        exact (OCF.Denis.psi_zero_eq_of_collapse_between s _ (denote s l) (denote s a) hlo hhi).trans hqe

/-- A finite normal I presentation, selected from the original index's
subterms using the existence proof above. -/
def normalIndexPair (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k)) : Term × Term :=
  let h := exists_normal_index s k hk hreg
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem normalIndexPair_spec (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k)) :
    let p := normalIndexPair s k hk hreg
    Subterm (.I p.1 p.2) k ∧ IsNormal s (.I p.1 p.2) ∧
      OCF.Denis.RegularIndex s (denote s (.I p.1 p.2)) ∧
      OCF.Denis.C s 0 (OCF.Denis.psi s (denote s (.I p.1 p.2)) 0) (denote s (.I p.1 p.2)) ∧
      OCF.Denis.psi s (denote s k) 0 = OCF.Denis.psi s (denote s (.I p.1 p.2)) 0 :=
  Classical.choose_spec (Classical.choose_spec (exists_normal_index s k hk hreg))

theorem normalIndexPair_rank_smaller (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k)) :
    sizeOf (normalIndexPair s k hk hreg).1 < sizeOf k :=
  (normalIndexPair_spec s k hk hreg).1.index_rank_size_lt

end
end T.Correspondence.Denis.Covering.ZeroIndex
