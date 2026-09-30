import Multi.term3.Denis.NormalSequenceCoverage

/-! Cofinality at represented ranks for limits of q |-> I(q,c).
The admissible fixed arguments include zero and every successor;
these are the rank-limit maps used in zero/successor collapse rules. -/

namespace OCF.Denis
open Ordinal

theorem I_fixed_argument_rank_strict (s : Supply) (c : O) (hc : ∀ q, c < I s q c)
    {q r : O} (hqr : q < r) : I s q c < I s r c :=
  I_lower_rank_closed s q r c c hqr (hc r)

theorem I_lt_rank_indexedSup (s : Supply) (r c q : O) (hr : IsLimit r)
    (hc : ∀ p, c < I s p c) (hq : q < r) :
    I s q c < indexedSup r (fun p => I s p c) :=
  lt_of_lt_of_le (I_fixed_argument_rank_strict s c hc (lt_succ_self q))
    (le_indexedSup r (fun p => I s p c) (succ_lt_limit hr hq))

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem normal_rank_interpolation (s : OCF.Denis.Supply) (r c : OCF.Denis.O)
    (hr : OCF.Denis.IsLimit r) (hbounded : OCF.Denis.RankBounded s r)
    (hc : ∀ q, c < OCF.Denis.I s q c)
    (t : Term) (ht : IsNormal s t)
    (hlt : denote s t < OCF.Denis.indexedSup r (fun q => OCF.Denis.I s q c)) :
    ∃ q, Represented s q ∧ q < r ∧ denote s t < OCF.Denis.I s q c := by
  classical
  have hrpos := (zero_lt_iff_ne_zero r).mpr hr.1
  have hm (p q : OCF.Denis.O) (hpq : p ≤ q) : OCF.Denis.I s p c ≤ OCF.Denis.I s q c := by
    rcases hpq with h | rfl
    · exact Or.inl (OCF.Denis.I_fixed_argument_rank_strict s c hc h)
    · exact le_refl _
  induction ht with
  | zero => exact ⟨0, ⟨.zero, .zero, rfl⟩, hrpos, OCF.Ordinal.lt_of_le_of_lt (zero_le c) (hc 0)⟩
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    obtain ⟨q, hq, hqr, huq, hvq⟩ := combine_represented_stages s r _ _ (fun q => OCF.Denis.I s q c) hm
      (ihu (OCF.Ordinal.lt_of_le_of_lt (le_add _ _) hlt))
      (ihv (OCF.Ordinal.lt_of_le_of_lt (right_le_add _ _) hlt))
    exact ⟨q, hq, hqr, OCF.Denis.I_addPrincipal s q c _ _ huq hvq⟩
  | @index p b hp hb hpl hbl ihp ihb =>
    by_cases hsmall : denote s (.I p b) < OCF.Denis.I s 0 c
    · exact ⟨0, ⟨.zero, .zero, rfl⟩, hrpos, hsmall⟩
    have hcx := OCF.Ordinal.lt_of_lt_of_le (hc 0) ((not_lt_iff_le _ _).mp hsmall)
    obtain ⟨q, hqr, hxq⟩ := (OCF.Denis.lt_indexedSup_iff r (fun q => OCF.Denis.I s q c) _).mp hlt
    have hpq : denote s p ≤ q := by
      apply (not_lt_iff_le q (denote s p)).mp
      intro hqp
      exact False.elim (OCF.Ordinal.lt_asymm hxq (OCF.Denis.I_lower_rank_closed s q (denote s p) (denote s b) c hqp hcx))
    have hpr := OCF.Ordinal.lt_of_le_of_lt hpq hqr
    obtain ⟨j, hj, hjr, hbj⟩ := ihb (OCF.Ordinal.lt_trans _ _ _ hbl hlt)
    obtain ⟨u, hu, hur, hpu, hju⟩ := combine_represented_stages s r (denote s p) j (fun q => q)
      (fun _ _ h => h)
      ⟨succ (denote s p), represented_succ s _ ⟨p, hp, rfl⟩, OCF.Denis.succ_lt_limit hr hpr, lt_succ_self _⟩
      ⟨succ j, represented_succ s j hj, OCF.Denis.succ_lt_limit hr hjr, lt_succ_self j⟩
    exact ⟨u, hu, hur, OCF.Denis.I_lower_rank_closed s (denote s p) u c (denote s b) hpu
      (OCF.Ordinal.lt_trans _ _ _ hbj (OCF.Denis.I_fixed_argument_rank_strict s c hc hju))⟩
  | @collapse k a hk ha hreg harg ihk iha =>
    by_cases hsmall : denote s (.psi k a) < OCF.Denis.I s 0 c
    · exact ⟨0, ⟨.zero, .zero, rfl⟩, hrpos, hsmall⟩
    have hcx := OCF.Ordinal.lt_of_lt_of_le (hc 0) ((not_lt_iff_le _ _).mp hsmall)
    have hkbound : denote s k < OCF.Denis.indexedSup r (fun q => OCF.Denis.I s q c) := by
      apply Classical.byContradiction
      intro hn
      have hdk := (not_lt_iff_le _ _).mp hn
      obtain ⟨q, hqr, hxq⟩ := (OCF.Denis.lt_indexedSup_iff r (fun q => OCF.Denis.I s q c) _).mp hlt
      have hqk := OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.I_lt_rank_indexedSup s r c q hr hc hqr) hdk
      have hq0k := OCF.Ordinal.le_trans (OCF.Denis.I_mono s q (zero_le c)) (Or.inl hqk)
      have hqx := OCF.Ordinal.lt_of_lt_of_le
        (OCF.Denis.rank_lt_psi_of_first_le s q (denote s k)
          (OCF.Denis.rankBounded_down s (Or.inl hqr) hbounded) hq0k)
        (OCF.Denis.psi_mono s _ 0 (denote s a) (zero_le _))
      have h := OCF.Denis.psi_closed s (denote s k) (denote s a) (OCF.Denis.I s q c)
        (OCF.Denis.C_index s _ _ q c (OCF.Denis.C_seed s _ _ q hqx) (OCF.Denis.C_seed s _ _ c hcx)) hqk
      exact OCF.Ordinal.lt_asymm hxq h
    obtain ⟨q, hq, hqr, hkq⟩ := ihk hkbound
    exact ⟨q, hq, hqr, OCF.Ordinal.lt_trans _ _ _
      (OCF.Denis.psi_lt s _ _ (OCF.Denis.regularIndex_regular s _ hreg)) hkq⟩

theorem rank_limit_coveringFundamentalSequence (s : OCF.Denis.Supply) (r c length : OCF.Denis.O)
    (hr : Represented s r) (hcRep : Represented s c) (hc : ∀ q, c < OCF.Denis.I s q c)
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s r length f) :
    CoveringFundamentalSequence s (OCF.Denis.indexedSup r (fun q => OCF.Denis.I s q c)) length
      (fun i => OCF.Denis.I s (f i) c) := by
  have hrlim := hf.normalSequence.fundamental.isLimit hl
  have hbounded : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact fun i hi => OCF.Denis.I_lt_rank_indexedSup s r c _ hrlim hc (hf.normalSequence.fundamental.below i hi)
  · exact fun i j hij hj => OCF.Denis.I_fixed_argument_rank_strict s c hc
      (hf.normalSequence.fundamental.strict i j hij hj)
  · intro x hx
    obtain ⟨q, hqr, hxq⟩ := (OCF.Denis.lt_indexedSup_iff r (fun q => OCF.Denis.I s q c) x).mp hx
    obtain ⟨i, hi, hqi⟩ := hf.normalSequence.fundamental.cofinal q hqr
    exact ⟨i, hi, OCF.Ordinal.lt_trans _ _ _ hxq (OCF.Denis.I_fixed_argument_rank_strict s c hc hqi)⟩
  · exact fun i hi hni => represented_I s _ c (hf.normalSequence.normal i hi hni) hcRep
  · intro x hx hxl
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨q, hq, hqr, hxq⟩ := normal_rank_interpolation s r c hrlim hbounded hc t ht hxl
    obtain ⟨i, hiRep, hi, hqi⟩ := hf.cofinal_normal q hq hqr
    exact ⟨i, hiRep, hi, OCF.Ordinal.lt_trans _ _ _ hxq (OCF.Denis.I_fixed_argument_rank_strict s c hc hqi)⟩

theorem limit_rank_zero_coveringFundamentalSequence (s : OCF.Denis.Supply) (r length : OCF.Denis.O)
    (hr : Represented s r) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s r length f) :
    CoveringFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) 0) length
      (fun i => OCF.Denis.I s (f i) 0) := by
  have hbounded : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  rw [← OCF.Denis.rankSup_eq_psi_first_limit_rank s r (hf.normalSequence.fundamental.isLimit hl) hbounded]
  exact rank_limit_coveringFundamentalSequence s r 0 length hr ⟨.zero, .zero, rfl⟩
    (fun q => OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨q, rfl⟩))) hl f hf

theorem limit_rank_succ_coveringFundamentalSequence (s : OCF.Denis.Supply) (r a length : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r 0) a) a)
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s r length f) :
    CoveringFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) (succ a)) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.psi s (OCF.Denis.I s r 0) a))) := by
  have hbounded : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  have hp := represented_psi_of_mem s _ a (represented_I s r 0 hr ⟨.zero, .zero, rfl⟩) ha
    (Or.inl ⟨r, rfl⟩) harg
  rw [← OCF.Denis.rankSuccSup_eq_psi_first_limit_rank_succ s r a
    (hf.normalSequence.fundamental.isLimit hl) hbounded harg]
  exact rank_limit_coveringFundamentalSequence s r _ length hr (represented_succ s _ hp)
    (fun q => OCF.Denis.succ_lt_I_succ s q _) hl f hf

theorem limit_rank_successor_index_zero_coveringFundamentalSequence (s : OCF.Denis.Supply)
    (r b length : OCF.Denis.O) (hr : Represented s r) (hb : Represented s b)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b)))
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s r length f) :
    CoveringFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.I s r b))) := by
  rw [OCF.Denis.limit_rank_successor_index_zero_eq s r b (hf.normalSequence.fundamental.isLimit hl) hmem]
  exact rank_limit_coveringFundamentalSequence s r _ length hr
    (represented_succ s _ (represented_I s r b hr hb)) (fun q => OCF.Denis.succ_lt_I_succ s q _) hl f hf

theorem limit_rank_successor_index_succ_coveringFundamentalSequence (s : OCF.Denis.Supply)
    (r b a length : OCF.Denis.O) (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a))
      (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a)
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s r length f) :
    CoveringFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.successorIndexBase s r b a))) := by
  rw [OCF.Denis.limit_rank_successor_index_succ_eq s r b a (hf.normalSequence.fundamental.isLimit hl) hmem harg]
  exact rank_limit_coveringFundamentalSequence s r _ length hr
    (represented_succ s _ (successorIndexBase_represented s r b a hr hb ha harg))
    (fun q => OCF.Denis.succ_lt_I_succ s q _) hl f hf

end
end T.Correspondence.Denis.Covering
