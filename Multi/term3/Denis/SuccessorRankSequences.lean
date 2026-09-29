import Multi.term3.Denis.CollapseTrees

/-! The successor-argument rule at every represented successor-rank
index. The argument may be uncountable. Starting above the preceding
collapse and iterating I(r,.) gives the next collapse value. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def indexIterFrom (s : Supply) (r b : O) : Nat → O
  | 0 => b
  | n + 1 => I s r (indexIterFrom s r b n)

theorem indexIterFrom_lt_succ (s : Supply) (r b : O) (hb : b < I s r b) (n : Nat) :
    indexIterFrom s r b n < indexIterFrom s r b (n + 1) := by
  induction n with
  | zero => exact hb
  | succ n ih => exact I_strict s r ih

theorem indexIterFrom_strict (s : Supply) (r b : O) (hb : b < I s r b)
    {n m : Nat} (h : n < m) : indexIterFrom s r b n < indexIterFrom s r b m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact lt_trans _ _ _ (ih h) (indexIterFrom_lt_succ s r b hb m)
    · exact indexIterFrom_lt_succ s r b hb n

theorem indexIterFrom_lt_sup (s : Supply) (r b : O) (hb : b < I s r b) (n : Nat) :
    indexIterFrom s r b n < sup (indexIterFrom s r b) :=
  lt_of_lt_of_le (indexIterFrom_lt_succ s r b hb n) (le_sup _ (n + 1))

theorem indexIterFrom_sup_fixedpoint (s : Supply) (r b : O) (hb : b < I s r b) :
    I s r (sup (indexIterFrom s r b)) = sup (indexIterFrom s r b) := by
  have hf : FundamentalSequence (sup (indexIterFrom s r b)) (indexIterFrom s r b) :=
    ⟨indexIterFrom_lt_sup s r b hb, fun _ _ h => indexIterFrom_strict s r b hb h,
      fun x hx => (lt_sup_iff _ x).mp hx⟩
  exact (I_fundamentalSequence s r _ _ hf).sup_eq.symm.trans (hf.shift 1).sup_eq

theorem indexIterFrom_lt_first_succ_rank (s : Supply) (r b : O)
    (hb : b < I s (succ r) 0) (n : Nat) : indexIterFrom s r b n < I s (succ r) 0 := by
  induction n with
  | zero => exact hb
  | succ n ih => exact I_lower_rank_closed s r (succ r) 0 _ (lt_succ_self r) ih

theorem indexIterFrom_sup_lt_first_succ_rank (s : Supply) (r b : O)
    (hb : b < I s (succ r) 0) : sup (indexIterFrom s r b) < I s (succ r) 0 := by
  obtain ⟨bound, hbound, hfb⟩ := small_nat
    (regularIndex_regular s _ (Or.inl ⟨succ r, rfl⟩))
    (indexIterFrom s r b) (indexIterFrom_lt_first_succ_rank s r b hb)
  exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun n => Or.inl (hfb n))) hbound

theorem succ_lt_I_succ (s : Supply) (r b : O) : succ b < I s r (succ b) := by
  have hb := lt_of_le_of_lt (index_le_I s r b) (I_strict s r (lt_succ_self b))
  exact regular_succ_lt (regularIndex_regular s _ (Or.inr ⟨r, b, rfl⟩)) hb

/-- A collapse below this canonical index cannot come from a larger
index. The statement allows arbitrary arguments and total indices. -/
theorem psi_index_le_of_below_successor_rank (s : Supply) (r k a : O)
    (hr : RankBounded s r) (hx : psi s k a < I s (succ r) 0) : k ≤ I s (succ r) 0 := by
  apply (not_lt_iff_le _ _).mp
  intro hlk
  have hmono := psi_mono_both s (I s (succ r) 0) k 0 a (Or.inl hlk) (zero_le a)
  have hsmall := lt_of_lt_of_le
    (succ_lt_limit (bounded_rank_zero_fundamentalSequence s r hr).isLimit
      (rank_lt_psi_first_succ_rank s r hr)) hmono
  have hlC := C_index s a (psi s k a) (succ r) 0 (C_seed s a _ _ hsmall) (C_zero s a _)
  exact lt_asymm (psi_closed s k a _ hlC hlk) hx

theorem C_successor_indexIterFrom_sup (s : Supply) (r a x : O) (hr : RankBounded s r)
    (hx : C s (succ a) (sup (indexIterFrom s r (succ (psi s (I s (succ r) 0) a)))) x)
    (hbound : x < I s (succ r) 0) :
    x < sup (indexIterFrom s r (succ (psi s (I s (succ r) 0) a))) := by
  let b := succ (psi s (I s (succ r) 0) a)
  let f := indexIterFrom s r b
  have hb : b < I s r b := succ_lt_I_succ s r _
  have hfix : I s r (sup f) = sup f := indexIterFrom_sup_fixedpoint s r b hb
  have hprincipal : AddPrincipal (sup f) := hfix ▸ I_addPrincipal s r (sup f)
  have hbup : b < sup f := indexIterFrom_lt_sup s r b hb 0
  have hpup : psi s (I s (succ r) 0) a < sup f := lt_trans _ _ _ (lt_succ_self _) hbup
  have h := (C_iff s (succ a) (sup f) x).mp hx
  clear hx
  induction h with
  | zero => exact lt_of_le_of_lt (zero_le b) hbup
  | seed hx => exact hx
  | @add u v hu hv ihu ihv =>
    exact hprincipal u v (ihu (lt_of_le_of_lt (le_add u v) hbound))
      (ihv (lt_of_le_of_lt (right_le_add u v) hbound))
  | @index q c hq hc ihq ihc =>
    have hqr := rank_le_of_I_lt_first_succ_rank s q c r hbound
    have hcup := ihc (lt_of_le_of_lt (index_le_I s q c) hbound)
    rcases hqr with hqr | hqr
    · have hlt := I_lower_rank_closed s q r (sup f) c hqr (hfix.symm ▸ hcup)
      rwa [hfix] at hlt
    · rw [hqr]
      have hlt := I_strict s r hcup
      rwa [hfix] at hlt
  | @collapse k c hc hk hkc hcc ihk ihc =>
    change psi s k c < _ at hbound ⊢
    exact lt_of_le_of_lt (psi_mono_both s k (I s (succ r) 0) c a
      (psi_index_le_of_below_successor_rank s r k c hr hbound)
      ((lt_succ_iff_le c a).mp hc)) hpup

theorem indexIterFrom_sup_eq_psi_successor_rank_succ (s : Supply) (r a : O)
    (hr : RankBounded s r) (ha : C s a (psi s (I s (succ r) 0) a) a) :
    sup (indexIterFrom s r (succ (psi s (I s (succ r) 0) a))) =
      psi s (I s (succ r) 0) (succ a) := by
  let l := I s (succ r) 0
  let p := psi s l a
  let target := psi s l (succ a)
  have hl : UncountableRegular l := regularIndex_regular s _ (Or.inl ⟨succ r, rfl⟩)
  have hstart : succ p < l := regular_succ_lt hl (psi_lt s l a hl)
  apply le_antisymm
  · have hmono : psi s l 0 ≤ target := psi_mono s l 0 (succ a) (zero_le _)
    have hrC : C s (succ a) target r := C_seed s _ _ _
      (lt_of_lt_of_le (rank_lt_psi_first_succ_rank s r hr) hmono)
    have hlC : C s (succ a) target l := C_mono_seed s _ _ _ hmono _
      (C_mono_argument s 0 (succ a) _ (zero_le _) _ (successor_rank_index_mem s r hr))
    have haC : C s (succ a) target a := C_mono_seed s _ _ _
      (psi_mono s l a (succ a) (Or.inl (lt_succ_self a))) a
      (C_mono_argument s a (succ a) _ (Or.inl (lt_succ_self a)) a ha)
    have hpC : C s (succ a) target p := C_collapse s _ _ l a (lt_succ_self a)
      (Or.inl ⟨succ r, rfl⟩) hlC haC
    have hstartC : C s (succ a) target (succ p) := by
      have h := C_add s (succ a) target p (succ 0) hpC
        (C_finite s (succ a) target (lt_of_le_of_lt (zero_le a) (lt_succ_self a)) 1)
      rwa [add_succ, add_zero] at h
    have hiC : ∀ n, C s (succ a) target (indexIterFrom s r (succ p) n) := by
      intro n
      induction n with
      | zero => exact hstartC
      | succ n ih => exact C_index s _ _ r _ hrC ih
    exact (sup_le_iff _ target).mpr (fun n => Or.inl
      (psi_closed s l (succ a) _ (hiC n) (indexIterFrom_lt_first_succ_rank s r (succ p) hstart n)))
  · exact psi_min s l (succ a) _
      ⟨Or.inl (indexIterFrom_sup_lt_first_succ_rank s r (succ p) hstart),
        fun x hx hxl => C_successor_indexIterFrom_sup s r a x hr hx hxl⟩

theorem successor_rank_succ_fundamentalSequence (s : Supply) (r a : O)
    (hr : RankBounded s r) (ha : C s a (psi s (I s (succ r) 0) a) a) :
    FundamentalSequence (psi s (I s (succ r) 0) (succ a))
      (indexIterFrom s r (succ (psi s (I s (succ r) 0) a))) := by
  rw [← indexIterFrom_sup_eq_psi_successor_rank_succ s r a hr ha]
  exact ⟨indexIterFrom_lt_sup s r _ (succ_lt_I_succ s r _),
    fun _ _ h => indexIterFrom_strict s r _ (succ_lt_I_succ s r _) h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem indexIterFrom_represented (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (n : Nat) :
    Represented s (OCF.Denis.indexIterFrom s r b n) := by
  induction n with
  | zero => exact hb
  | succ n ih => exact represented_I s r _ hr ih

theorem successor_rank_succ_dense (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) a) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) := by
  have hrank : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  have hl := represented_I s (succ r) 0 (represented_succ s r hr) ⟨.zero, .zero, rfl⟩
  have hp := represented_psi_of_mem s _ a hl ha (Or.inl ⟨succ r, rfl⟩) harg
  exact dense_of_normal_sequence s _ _ (OCF.Denis.successor_rank_succ_fundamentalSequence s r a hrank harg)
    (indexIterFrom_represented s r _ hr (represented_succ s _ hp))

/-- Covers the entire normal successor-argument branch at these
indices. The predecessor's admissibility is derived from the parent. -/
theorem successor_rank_normal_succ_dense (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) (succ a)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) :=
  successor_rank_succ_dense s r a hr (represented_predecessor s a ha)
    (OCF.Denis.psi_predecessor_argument_normal_general s _ a harg)

theorem revised_successor_rank_normal_succ_fundamentalSequence (s : OCF.Denis.Supply)
    (r a : OCF.Denis.O) (hr : Represented s r) (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) (succ a)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos
      (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ r, rfl⟩))))
    (successor_rank_normal_succ_dense s r a hr ha harg)

theorem revised_successor_rank_normal_succ_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r a : OCF.Denis.O) (hr : Represented s r) (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) (succ a)) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) OCF.Denis.omega
      (fun i => revisedValue s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a))
        (OCF.Denis.finiteIndex i)) :=
  ⟨(revised_successor_rank_normal_succ_fundamentalSequence s r a hr ha harg).transfinite,
    fun _ _ _ => revisedValue_represented s _ _⟩

theorem successor_rank_normal_succ_cofinality (s : OCF.Denis.Supply)
    (r a : OCF.Denis.O) (hr : Represented s r) (ha : Represented s (succ a))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a)) (succ a)) :
    OCF.Denis.cofinality (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (succ a))
      (revised_successor_rank_normal_succ_fundamentalSequence s r a hr ha harg).isLimit = OCF.Denis.omega :=
  OCF.Denis.cofinality_eq_omega_of_fundamentalSequence
    (revised_successor_rank_normal_succ_fundamentalSequence s r a hr ha harg)

/-- Transfer an arbitrary ordinal-length normal fundamental sequence
through a canonical successor-rank collapse. Admissibility of every
approximant follows from the parent's admissibility below the index. -/
theorem successor_rank_limit_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r a length : OCF.Denis.O) (hr : Represented s r) (hl : 0 < length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s a length f)
    (habound : a < OCF.Denis.I s (succ r) 0)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) a) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) length
      (fun i => OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (f i)) := by
  have hrank : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  apply psi_normalFundamentalSequence s _ a length
    (represented_I s (succ r) 0 (represented_succ s r hr) ⟨.zero, .zero, rfl⟩)
    (Or.inl ⟨succ r, rfl⟩) hl f hf
  · intro i _
    exact OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ 0 (f i) (zero_le _)) _
      (OCF.Denis.C_mono_argument s 0 (f i) _ (zero_le _) _
        (OCF.Denis.successor_rank_index_mem s r hrank))
  · intro i hi
    exact OCF.Denis.C_seed s _ _ _
      (OCF.Denis.psi_argument_normal_below s _ a (f i) habound harg (hf.fundamental.below i hi))

theorem successor_rank_normal_limit_dense (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a)
    (habound : a < OCF.Denis.I s (succ r) 0)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) a) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) :=
  (successor_rank_limit_normalFundamentalSequence s r a OCF.Denis.omega hr
    (OCF.Denis.finite_lt_omega 0) _ (revised_normalFundamentalSequence s a ha hd) habound harg).omega_dense

/-- An interval of arguments, with no assumed density: every normal
argument at or below the first diagonal collapse is covered. The rank
is an arbitrary represented ordinal, including uncountable ranks. -/
theorem successor_rank_bounded_argument_dense (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) (a : Term) (ha : IsNormal s a)
    (habound : denote s a ≤ OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (denote s a)) := by
  classical
  have hrank : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  have hasmall : denote s a < OCF.Denis.I s 0 0 := OCF.Ordinal.lt_of_le_of_lt habound
    (OCF.Denis.psi_lt s _ _ (OCF.Denis.first_regular s))
  have harg := (OCF.Denis.successor_rank_small_argument_mem s r (denote s a) hrank hasmall).2
  by_cases hz : denote s a = 0
  · rw [hz]
    exact successor_rank_zero_dense s r hr
  by_cases hs : ∃ b, denote s a = succ b
  · obtain ⟨b, hb⟩ := hs
    rw [hb] at harg ⊢
    exact successor_rank_normal_succ_dense s r b hr ⟨a, ha, hb⟩ harg
  · exact successor_rank_normal_limit_dense s r (denote s a) hr ⟨hz, hs⟩
      (normal_dense_below_first_diagonal s a ha habound ⟨hz, hs⟩)
      (OCF.Ordinal.lt_of_lt_of_le hasmall (OCF.Denis.I_lower_bound s (succ r) 0)) harg

theorem revised_successor_rank_bounded_argument_fundamentalSequence (s : OCF.Denis.Supply)
    (r : OCF.Denis.O) (hr : Represented s r) (a : Term) (ha : IsNormal s a)
    (habound : denote s a ≤ OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (denote s a))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) (denote s a))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos
      (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ r, rfl⟩))))
    (successor_rank_bounded_argument_dense s r hr a ha habound)

end
end T.Correspondence.Denis.Covering
