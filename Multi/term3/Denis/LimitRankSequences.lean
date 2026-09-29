import Multi.term3.Denis.SuccessorRankSequences

/-! The zero-argument collapse at a limit rank. Its value is the
supremum of the first indices at smaller ranks. A normal fundamental
sequence for the rank induces one for the collapse, including ordinal
domains of uncountable cofinality. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def rankSup (s : Supply) (r : O) : O := indexedSup r (fun q => I s q 0)

theorem I_zero_rank_strict (s : Supply) {q r : O} (h : q < r) : I s q 0 < I s r 0 := by
  rw [I_zero, I_zero]
  exact first_rank_strict s h

theorem first_lt_rankSup (s : Supply) (r q : O) (hr : IsLimit r) (hq : q < r) :
    I s q 0 < rankSup s r :=
  lt_of_lt_of_le (I_zero_rank_strict s (lt_succ_self q))
    (le_indexedSup r (fun q => I s q 0) (succ_lt_limit hr hq))

theorem rankSup_pos (s : Supply) (r : O) (hr : IsLimit r) : 0 < rankSup s r :=
  lt_trans _ _ _ (regular_pos (first_regular s))
    (first_lt_rankSup s r 0 hr ((zero_lt_iff_ne_zero r).mpr hr.1))

theorem rankSup_add_closed (s : Supply) (r : O) (hr : IsLimit r) : AddPrincipal (rankSup s r) := by
  intro x y hx hy
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q 0) x).mp hx
  obtain ⟨p, hpr, hyp⟩ := (lt_indexedSup_iff r (fun q => I s q 0) y).mp hy
  obtain ⟨t, htr, hqt, hpt⟩ := two_bounded_below_limit hr hqr hpr
  exact lt_trans _ _ _ (I_addPrincipal s t 0 x y
    (lt_trans _ _ _ hxq (I_zero_rank_strict s hqt))
    (lt_trans _ _ _ hyp (I_zero_rank_strict s hpt))) (first_lt_rankSup s r t hr htr)

theorem rankSup_I_closed (s : Supply) (r q x : O) (hr : IsLimit r)
    (hq : q < r) (hx : x < rankSup s r) : I s q x < rankSup s r := by
  obtain ⟨p, hpr, hxp⟩ := (lt_indexedSup_iff r (fun q => I s q 0) x).mp hx
  obtain ⟨t, htr, hqt, hpt⟩ := two_bounded_below_limit hr hq hpr
  have hxt := lt_trans _ _ _ hxp (I_zero_rank_strict s hpt)
  exact lt_trans _ _ _ (I_lower_rank_closed s q t 0 x hqt hxt) (first_lt_rankSup s r t hr htr)

theorem rankSup_lt_first (s : Supply) (r : O) (hr : RankBounded s r) : rankSup s r < I s r 0 := by
  have hrl : r < I s r 0 := by rw [I_zero]; exact rank_lt_first_of_bounded s r hr
  obtain ⟨bound, hbound, hfb⟩ := (regularIndex_regular s _ (Or.inl ⟨r, rfl⟩)).2 r hrl
    (fun i => I s (type ((representative r).below i)) 0)
    (fun i => I_zero_rank_strict s (initial_lt r i))
  exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun i => Or.inl (hfb i))) hbound

theorem rank_lt_of_I_lt_first (s : Supply) (q b r : O) (h : I s q b < I s r 0) : q < r := by
  rcases lt_total q r with hqr | hqr | hrq
  · exact hqr
  · rw [hqr] at h
    exact False.elim (lt_irrefl _ (lt_of_lt_of_le h (I_mono s r (zero_le b))))
  · exact False.elim (lt_irrefl _ (lt_of_lt_of_le (lt_trans _ _ _ h (I_zero_rank_strict s hrq))
      (I_mono s q (zero_le b))))

theorem C_zero_rankSup (s : Supply) (r : O) (hr : IsLimit r) (x : O)
    (hx : C s 0 (rankSup s r) x) (hbound : x < I s r 0) : x < rankSup s r := by
  have h := (C_iff s 0 (rankSup s r) x).mp hx
  clear hx
  induction h with
  | zero => exact rankSup_pos s r hr
  | seed hx => exact hx
  | @add u v hu hv ihu ihv =>
    exact rankSup_add_closed s r hr u v (ihu (lt_of_le_of_lt (le_add u v) hbound))
      (ihv (lt_of_le_of_lt (right_le_add u v) hbound))
  | @index q b hq hb ihq ihb =>
    exact rankSup_I_closed s r q b hr (rank_lt_of_I_lt_first s q b r hbound)
      (ihb (lt_of_le_of_lt (index_le_I s q b) hbound))
  | collapse hb _ _ _ _ _ => exact False.elim (not_lt_zero _ hb)

theorem rankSup_eq_psi_first_limit_rank (s : Supply) (r : O) (hr : IsLimit r)
    (hbounded : RankBounded s r) : rankSup s r = psi s (I s r 0) 0 := by
  apply le_antisymm
  · apply indexedSup_le
    intro q hqr
    have hrpsi := rank_lt_psi_of_first_le s r (I s r 0) hbounded (le_refl _)
    have hqC := C_seed s 0 (psi s (I s r 0) 0) q (lt_trans _ _ _ hqr hrpsi)
    exact Or.inl (psi_closed s _ 0 _ (C_index s _ _ q 0 hqC (C_zero s _ _))
      (I_zero_rank_strict s hqr))
  · exact psi_min s _ _ _ ⟨Or.inl (rankSup_lt_first s r hbounded), C_zero_rankSup s r hr⟩

theorem limit_rank_zero_transfiniteFundamentalSequence (s : Supply) (r length : O)
    (hbounded : RankBounded s r) (hl : 0 < length) (f : O → O)
    (hf : TransfiniteFundamentalSequence r length f) :
    TransfiniteFundamentalSequence (psi s (I s r 0) 0) length (fun i => I s (f i) 0) := by
  have hr := hf.isLimit hl
  rw [← rankSup_eq_psi_first_limit_rank s r hr hbounded]
  refine ⟨fun i hi => first_lt_rankSup s r _ hr (hf.below i hi),
    fun i j hij hj => I_zero_rank_strict s (hf.strict i j hij hj), ?_⟩
  intro x hx
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q 0) x).mp hx
  obtain ⟨i, hi, hqi⟩ := hf.cofinal q hqr
  exact ⟨i, hi, lt_trans _ _ _ hxq (I_zero_rank_strict s hqi)⟩

theorem first_rank_index_mem (s : Supply) (r a : O) (hr : RankBounded s r) :
    C s a (psi s (I s r 0) a) (I s r 0) := by
  have hrp := rank_lt_psi_of_first_le s r (I s r 0) hr (le_refl _)
  exact C_index s a _ r 0
    (C_seed s a _ r (lt_of_lt_of_le hrp (psi_mono s _ 0 a (zero_le a)))) (C_zero s a _)

theorem psi_index_le_of_below_first_rank (s : Supply) (r k a : O)
    (hr : RankBounded s r) (hx : psi s k a < I s r 0) : k ≤ I s r 0 := by
  apply (not_lt_iff_le _ _).mp
  intro hlk
  have hrp := rank_lt_psi_of_first_le s r (I s r 0) hr (le_refl _)
  have hsmall := lt_of_lt_of_le hrp (psi_mono_both s (I s r 0) k 0 a (Or.inl hlk) (zero_le a))
  have hlC := C_index s a (psi s k a) r 0 (C_seed s a _ r hsmall) (C_zero s a _)
  exact lt_asymm (psi_closed s k a _ hlC hlk) hx

def rankSuccSup (s : Supply) (r b : O) : O := indexedSup r (fun q => I s q (succ b))

theorem I_succ_rank_strict (s : Supply) {q r : O} (b : O) (h : q < r) :
    I s q (succ b) < I s r (succ b) :=
  I_lower_rank_closed s q r (succ b) (succ b) h (succ_lt_I_succ s r b)

theorem I_succ_lt_rankSuccSup (s : Supply) (r q b : O) (hr : IsLimit r) (hq : q < r) :
    I s q (succ b) < rankSuccSup s r b :=
  lt_of_lt_of_le (I_succ_rank_strict s b (lt_succ_self q))
    (le_indexedSup r (fun q => I s q (succ b)) (succ_lt_limit hr hq))

theorem base_lt_rankSuccSup (s : Supply) (r b : O) (hr : IsLimit r) : b < rankSuccSup s r b :=
  lt_trans _ _ _ (lt_trans _ _ _ (lt_succ_self b) (succ_lt_I_succ s 0 b))
    (I_succ_lt_rankSuccSup s r 0 b hr ((zero_lt_iff_ne_zero r).mpr hr.1))

theorem rankSuccSup_add_closed (s : Supply) (r b : O) (hr : IsLimit r) :
    AddPrincipal (rankSuccSup s r b) := by
  intro x y hx hy
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q (succ b)) x).mp hx
  obtain ⟨p, hpr, hyp⟩ := (lt_indexedSup_iff r (fun q => I s q (succ b)) y).mp hy
  obtain ⟨t, htr, hqt, hpt⟩ := two_bounded_below_limit hr hqr hpr
  exact lt_trans _ _ _ (I_addPrincipal s t (succ b) x y
    (lt_trans _ _ _ hxq (I_succ_rank_strict s b hqt))
    (lt_trans _ _ _ hyp (I_succ_rank_strict s b hpt))) (I_succ_lt_rankSuccSup s r t b hr htr)

theorem rankSuccSup_I_closed (s : Supply) (r q b x : O) (hr : IsLimit r)
    (hq : q < r) (hx : x < rankSuccSup s r b) : I s q x < rankSuccSup s r b := by
  obtain ⟨p, hpr, hxp⟩ := (lt_indexedSup_iff r (fun q => I s q (succ b)) x).mp hx
  obtain ⟨t, htr, hqt, hpt⟩ := two_bounded_below_limit hr hq hpr
  exact lt_trans _ _ _ (I_lower_rank_closed s q t (succ b) x hqt
    (lt_trans _ _ _ hxp (I_succ_rank_strict s b hpt))) (I_succ_lt_rankSuccSup s r t b hr htr)

theorem rankSuccSup_lt_first (s : Supply) (r b : O) (hr : RankBounded s r)
    (hb : b < I s r 0) : rankSuccSup s r b < I s r 0 := by
  have hreg := regularIndex_regular s _ (Or.inl ⟨r, rfl⟩)
  have hrl : r < I s r 0 := by rw [I_zero]; exact rank_lt_first_of_bounded s r hr
  have hs := regular_succ_lt hreg hb
  obtain ⟨bound, hbound, hfb⟩ := hreg.2 r hrl
    (fun i => I s (type ((representative r).below i)) (succ b))
    (fun i => I_lower_rank_closed s _ r 0 _ (initial_lt r i) hs)
  exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun i => Or.inl (hfb i))) hbound

theorem C_successor_rankSuccSup (s : Supply) (r a : O) (hr : IsLimit r)
    (hbounded : RankBounded s r) (x : O)
    (hx : C s (succ a) (rankSuccSup s r (psi s (I s r 0) a)) x) (hbound : x < I s r 0) :
    x < rankSuccSup s r (psi s (I s r 0) a) := by
  have h := (C_iff s _ _ x).mp hx
  clear hx
  induction h with
  | zero => exact lt_of_le_of_lt (zero_le _) (base_lt_rankSuccSup s r _ hr)
  | seed hx => exact hx
  | @add u v hu hv ihu ihv =>
    exact rankSuccSup_add_closed s r _ hr u v (ihu (lt_of_le_of_lt (le_add u v) hbound))
      (ihv (lt_of_le_of_lt (right_le_add u v) hbound))
  | @index q b hq hb ihq ihb =>
    exact rankSuccSup_I_closed s r q _ b hr (rank_lt_of_I_lt_first s q b r hbound)
      (ihb (lt_of_le_of_lt (index_le_I s q b) hbound))
  | @collapse k b hb hk hkc hbc ihk ihb =>
    change psi s k b < _ at hbound ⊢
    exact lt_of_le_of_lt (psi_mono_both s k (I s r 0) b a
      (psi_index_le_of_below_first_rank s r k b hbounded hbound) ((lt_succ_iff_le b a).mp hb))
      (base_lt_rankSuccSup s r _ hr)

theorem rankSuccSup_eq_psi_first_limit_rank_succ (s : Supply) (r a : O) (hr : IsLimit r)
    (hbounded : RankBounded s r) (ha : C s a (psi s (I s r 0) a) a) :
    rankSuccSup s r (psi s (I s r 0) a) = psi s (I s r 0) (succ a) := by
  let l := I s r 0
  let p := psi s l a
  let target := psi s l (succ a)
  have hreg := regularIndex_regular s l (Or.inl ⟨r, rfl⟩)
  apply le_antisymm
  · have hmono := psi_mono s l a (succ a) (Or.inl (lt_succ_self a))
    have haC := C_mono_seed s _ _ _ hmono a
      (C_mono_argument s a (succ a) _ (Or.inl (lt_succ_self a)) a ha)
    have hpC : C s (succ a) target p := C_collapse s _ _ l a (lt_succ_self a) (Or.inl ⟨r, rfl⟩)
      (first_rank_index_mem s r (succ a) hbounded) haC
    have hsC : C s (succ a) target (succ p) := by
      have h := C_add s _ _ p (succ 0) hpC
        (C_finite s (succ a) target (lt_of_le_of_lt (zero_le a) (lt_succ_self a)) 1)
      rwa [add_succ, add_zero] at h
    apply indexedSup_le
    intro q hqr
    have hqt : q < target := lt_trans _ _ _ hqr (lt_of_lt_of_le
      (rank_lt_psi_of_first_le s r l hbounded (le_refl _)) (psi_mono s l 0 (succ a) (zero_le _)))
    exact Or.inl (psi_closed s l (succ a) _
      (C_index s _ _ q (succ p) (C_seed s _ _ q hqt) hsC)
      (I_lower_rank_closed s q r 0 _ hqr (regular_succ_lt hreg (psi_lt s l a hreg))))
  · exact psi_min s l (succ a) _
      ⟨Or.inl (rankSuccSup_lt_first s r p hbounded (psi_lt s l a hreg)),
        C_successor_rankSuccSup s r a hr hbounded⟩

theorem limit_rank_succ_transfiniteFundamentalSequence (s : Supply) (r a length : O)
    (hbounded : RankBounded s r) (ha : C s a (psi s (I s r 0) a) a)
    (hl : 0 < length) (f : O → O) (hf : TransfiniteFundamentalSequence r length f) :
    TransfiniteFundamentalSequence (psi s (I s r 0) (succ a)) length
      (fun i => I s (f i) (succ (psi s (I s r 0) a))) := by
  have hr := hf.isLimit hl
  rw [← rankSuccSup_eq_psi_first_limit_rank_succ s r a hr hbounded ha]
  refine ⟨fun i hi => I_succ_lt_rankSuccSup s r _ _ hr (hf.below i hi),
    fun i j hij hj => I_succ_rank_strict s _ (hf.strict i j hij hj), ?_⟩
  intro x hx
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q (succ (psi s (I s r 0) a))) x).mp hx
  obtain ⟨i, hi, hqi⟩ := hf.cofinal q hqr
  exact ⟨i, hi, lt_trans _ _ _ hxq (I_succ_rank_strict s _ hqi)⟩

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem limit_rank_zero_normalFundamentalSequence (s : OCF.Denis.Supply) (r length : OCF.Denis.O)
    (hr : Represented s r) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : NormalFundamentalSequence s r length f) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) 0) length
      (fun i => OCF.Denis.I s (f i) 0) := by
  have hbounded : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  exact ⟨OCF.Denis.limit_rank_zero_transfiniteFundamentalSequence s r length hbounded hl f hf.fundamental,
    fun i hi hn => represented_I s _ 0 (hf.normal i hi hn) ⟨.zero, .zero, rfl⟩⟩

theorem limit_rank_succ_normalFundamentalSequence (s : OCF.Denis.Supply) (r a length : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r 0) a) a)
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : NormalFundamentalSequence s r length f) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) (succ a)) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.psi s (OCF.Denis.I s r 0) a))) := by
  have hbounded : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  have hp := represented_psi_of_mem s _ a (represented_I s r 0 hr ⟨.zero, .zero, rfl⟩) ha
    (Or.inl ⟨r, rfl⟩) harg
  exact ⟨OCF.Denis.limit_rank_succ_transfiniteFundamentalSequence s r a length hbounded harg hl f hf.fundamental,
    fun i hi hn => represented_I s _ _ (hf.normal i hi hn) (represented_succ s _ hp)⟩

/-- A concrete collapse whose minimal domain is uncountable. -/
theorem uncountable_rank_zero_normalFundamentalSequence (s : OCF.Denis.Supply) :
    NormalFundamentalSequence s
      (OCF.Denis.psi s (OCF.Denis.I s (OCF.Denis.I s 0 0) 0) 0) (OCF.Denis.I s 0 0)
      (fun i => OCF.Denis.I s i 0) :=
  limit_rank_zero_normalFundamentalSequence s _ _ ⟨omega1, omega1_isNormal s, rfl⟩
    (OCF.Denis.regular_pos (OCF.Denis.first_regular s)) (fun i => i)
    (regular_normalFundamentalSequence s _ (OCF.Denis.first_regular s))

theorem uncountable_rank_zero_cofinality (s : OCF.Denis.Supply) :
    OCF.Denis.cofinality (OCF.Denis.psi s (OCF.Denis.I s (OCF.Denis.I s 0 0) 0) 0)
      ((uncountable_rank_zero_normalFundamentalSequence s).fundamental.isLimit
        (OCF.Denis.regular_pos (OCF.Denis.first_regular s))) = OCF.Denis.I s 0 0 :=
  (OCF.Denis.cofinality_eq_of_transfiniteFundamentalSequence
    (uncountable_rank_zero_normalFundamentalSequence s).fundamental
    (OCF.Denis.regular_pos (OCF.Denis.first_regular s))).trans
      (OCF.Denis.cofinality_regular _ (OCF.Denis.first_regular s))

theorem not_dense_uncountable_rank_zero (s : OCF.Denis.Supply) :
    ¬ DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (OCF.Denis.I s 0 0) 0) 0) := by
  apply not_dense_of_uncountable_cofinality s _
    ((uncountable_rank_zero_normalFundamentalSequence s).fundamental.isLimit
      (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
  rw [uncountable_rank_zero_cofinality]
  exact (OCF.Denis.first_regular s).1

end
end T.Correspondence.Denis.Covering
