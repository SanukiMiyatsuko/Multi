import Multi.term3.Denis.SuccessorIndexSequences

/-! Successor arguments at successor indices. The preceding collapse
need not have the index in its closure: the base includes the preceding
I-value as well as the preceding collapse. Only membership at the parent
is required. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem C_successor_index_of_predecessor_lt_seed (s : Supply) (cutoff seed r b : O)
    (h : I s r b < seed) : C s cutoff seed (I s r (succ b)) := by
  have hr := lt_of_le_of_lt (rank_le_I s r b) h
  have hb := lt_of_le_of_lt (index_le_I s r b) h
  have hone : succ 0 < seed := lt_trans _ _ _
    (lt_of_lt_of_le (lt_trans _ _ _ (finite_lt_omega 1) (first_regular s).1) (I_lower_bound s r b)) h
  have hs := C_add s cutoff seed b (succ 0) (C_seed s cutoff seed b hb) (C_seed s cutoff seed _ hone)
  rw [add_succ, add_zero] at hs
  exact C_index s cutoff seed r (succ b) (C_seed s cutoff seed r hr) hs

/-- For a bounded rank, index membership is equivalent to the second
parameter being below the collapse; it is not an additional axiom. -/
theorem C_successor_index_iff_parameter (s : Supply) (r b a : O) (hr : RankBounded s r) :
    C s a (psi s (I s r (succ b)) a) (I s r (succ b)) ↔
      b < psi s (I s r (succ b)) a := by
  refine ⟨fun h => lt_of_le_of_lt (index_le_I s r b)
    (predecessor_index_lt_psi_of_mem s r b a h), ?_⟩
  intro hb
  have hrlt : r < psi s (I s r (succ b)) a :=
    lt_of_lt_of_le (rank_lt_psi_of_first_le s r _ hr (I_mono s r (zero_le _)))
    (psi_mono s _ 0 a (zero_le a))
  have hone : succ 0 < psi s (I s r (succ b)) a := lt_of_lt_of_le
    (lt_trans _ _ _ (finite_lt_omega 1) (first_regular s).1) (first_le_psi_successor_index s r b a)
  have hs := C_add s a _ b (succ 0) (C_seed s a _ b hb) (C_seed s a _ _ hone)
  rw [add_succ, add_zero] at hs
  exact C_index s a _ r (succ b) (C_seed s a _ r hrlt) hs

theorem C_successor_index_of_small_parameter (s : Supply) (r b a : O)
    (hr : RankBounded s r) (hb : b < I s 0 0) :
    C s a (psi s (I s r (succ b)) a) (I s r (succ b)) :=
  (C_successor_index_iff_parameter s r b a hr).mpr
    (lt_of_lt_of_le hb (first_le_psi_successor_index s r b a))

theorem C_successor_index_of_parameter_le_rank (s : Supply) (r b a : O)
    (hr : RankBounded s r) (hb : b ≤ r) :
    C s a (psi s (I s r (succ b)) a) (I s r (succ b)) :=
  (C_successor_index_iff_parameter s r b a hr).mpr (lt_of_le_of_lt hb
    (lt_of_lt_of_le (rank_lt_psi_of_first_le s r _ hr (I_mono s r (zero_le _)))
      (psi_mono s _ 0 a (zero_le a))))

/-- A collapse from a larger index cannot fall in the open gap
between consecutive I-values. No regularity of the larger index is needed. -/
theorem psi_successor_index_gap (s : Supply) (r b k a : O)
    (hk : I s r (succ b) < k) (h : psi s k a < I s r (succ b)) :
    psi s k a ≤ I s r b := by
  apply (not_lt_iff_le _ _).mp
  intro hbase
  exact lt_asymm (psi_closed s k a _
    (C_successor_index_of_predecessor_lt_seed s a _ r b hbase) hk) h

theorem C_succ_successor_index_bound (s : Supply) (r b a d : O)
    (hbase : I s r b < d) (hpsi : psi s (I s r (succ b)) a < d)
    (hadd : AddPrincipal d) (hI : ∀ q, q < r → ∀ x, x < d → I s q x < d)
    (x : O) (hx : C s (succ a) d x) (hbound : x < I s r (succ b)) : x < d := by
  have h := (C_iff s _ _ x).mp hx
  clear hx
  induction h with
  | zero => exact lt_of_le_of_lt (zero_le _) hbase
  | seed hx => exact hx
  | @add u v hu hv ihu ihv =>
    exact hadd u v (ihu (lt_of_le_of_lt (le_add u v) hbound))
      (ihv (lt_of_le_of_lt (right_le_add u v) hbound))
  | @index q c hq hc ihq ihc =>
    rcases lt_total q r with hqr | hqr | hrq
    · exact hI q hqr c (ihc (lt_of_le_of_lt (index_le_I s q c) hbound))
    · exact lt_of_le_of_lt (I_successor_gap s r b q c (Or.inr hqr.symm) hbound) hbase
    · exact lt_of_le_of_lt (I_successor_gap s r b q c (Or.inl hrq) hbound) hbase
  | @collapse k c hc hk hkc hcc ihk ihc =>
    change psi s k c < _ at hbound ⊢
    rcases lt_total k (I s r (succ b)) with hkl | hkl | hlk
    · exact lt_of_le_of_lt (psi_mono_both s k _ c a (Or.inl hkl)
        ((lt_succ_iff_le c a).mp hc)) hpsi
    · exact lt_of_le_of_lt (psi_mono_both s k _ c a (Or.inr hkl)
        ((lt_succ_iff_le c a).mp hc)) hpsi
    · exact lt_of_le_of_lt (psi_successor_index_gap s r b k c hlk hbound) hbase

def successorIndexBase (s : Supply) (r b a : O) : O :=
  I s r b + psi s (I s r (succ b)) a

theorem successorIndexBase_pos (s : Supply) (r b a : O) : 0 < successorIndexBase s r b a :=
  lt_of_lt_of_le (lt_of_lt_of_le (regular_pos (first_regular s)) (I_lower_bound s r b)) (le_add _ _)

theorem successorIndexBase_lt_index (s : Supply) (r b a : O) :
    successorIndexBase s r b a < I s r (succ b) := by
  have hreg := regularIndex_regular s _ (Or.inr ⟨r, b, rfl⟩)
  exact regular_add_closed hreg (I_strict s r (lt_succ_self b)) (psi_lt s _ a hreg)

theorem successorIndexBase_mem (s : Supply) (r b a : O)
    (hmem : C s (succ a) (psi s (I s r (succ b)) (succ a)) (I s r (succ b)))
    (ha : C s a (psi s (I s r (succ b)) a) a) :
    C s (succ a) (psi s (I s r (succ b)) (succ a)) (successorIndexBase s r b a) := by
  have haC := C_mono_seed s _ _ _ (psi_mono s _ a (succ a) (Or.inl (lt_succ_self a))) a
    (C_mono_argument s a (succ a) _ (Or.inl (lt_succ_self a)) a ha)
  exact C_add s _ _ _ _ (C_predecessor_index s _ _ r b hmem)
    (C_collapse s _ _ _ a (lt_succ_self a) (Or.inr ⟨r, b, rfl⟩) hmem haC)

theorem successorIndexBase_succ_mem (s : Supply) (r b a : O)
    (hmem : C s (succ a) (psi s (I s r (succ b)) (succ a)) (I s r (succ b)))
    (ha : C s a (psi s (I s r (succ b)) a) a) :
    C s (succ a) (psi s (I s r (succ b)) (succ a)) (succ (successorIndexBase s r b a)) := by
  have h := C_add s _ _ _ (succ 0) (successorIndexBase_mem s r b a hmem ha)
    (C_finite s (succ a) _ (lt_of_le_of_lt (zero_le a) (lt_succ_self a)) 1)
  rwa [add_succ, add_zero] at h

theorem rank_zero_successor_index_succ_eq (s : Supply) (b a : O)
    (hmem : C s (succ a) (psi s (I s 0 (succ b)) (succ a)) (I s 0 (succ b)))
    (ha : C s a (psi s (I s 0 (succ b)) a) a) :
    psi s (I s 0 (succ b)) (succ a) = sup (repeatAdd (successorIndexBase s 0 b a)) := by
  let k := I s 0 (succ b)
  let p := successorIndexBase s 0 b a
  let d := psi s k (succ a)
  have hreg := regularIndex_regular s k (Or.inr ⟨0, b, rfl⟩)
  have hp := successorIndexBase_pos s 0 b a
  have hpk := successorIndexBase_lt_index s 0 b a
  have hpM : p < sup (repeatAdd p) := by
    simpa only [repeatAdd, add_zero] using repeatAdd_lt_sup p hp 1
  apply le_antisymm
  · exact psi_min s k (succ a) _ ⟨Or.inl (repeatAdd_sup_lt_regular p k hreg hpk),
      C_succ_successor_index_bound s 0 b a _
        (lt_of_le_of_lt (le_add _ _) hpM) (lt_of_le_of_lt (right_le_add _ _) hpM)
        (repeatAdd_sup_addPrincipal p) (fun q hq => False.elim (not_lt_zero q hq))⟩
  · have hC : ∀ n, C s (succ a) d (repeatAdd p n) := by
      intro n
      induction n with
      | zero => exact C_zero s _ _
      | succ n ih => exact C_add s _ _ p _ (successorIndexBase_mem s 0 b a hmem ha) ih
    exact (sup_le_iff _ d).mpr (fun n => Or.inl
      (psi_closed s k (succ a) _ (hC n) (repeatAdd_lt_regular p k hreg hpk n)))

theorem rank_zero_successor_index_succ_fundamentalSequence (s : Supply) (b a : O)
    (hmem : C s (succ a) (psi s (I s 0 (succ b)) (succ a)) (I s 0 (succ b)))
    (ha : C s a (psi s (I s 0 (succ b)) a) a) :
    FundamentalSequence (psi s (I s 0 (succ b)) (succ a))
      (repeatAdd (successorIndexBase s 0 b a)) := by
  rw [rank_zero_successor_index_succ_eq s b a hmem ha]
  have hp := successorIndexBase_pos s 0 b a
  exact ⟨repeatAdd_lt_sup _ hp, fun _ _ h => repeatAdd_strict _ hp h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

theorem successor_rank_successor_index_succ_eq (s : Supply) (r b a : O)
    (hmem : C s (succ a) (psi s (I s (succ r) (succ b)) (succ a)) (I s (succ r) (succ b)))
    (ha : C s a (psi s (I s (succ r) (succ b)) a) a) :
    psi s (I s (succ r) (succ b)) (succ a) =
      sup (indexIterFrom s r (succ (successorIndexBase s (succ r) b a))) := by
  let k := I s (succ r) (succ b)
  let p := successorIndexBase s (succ r) b a
  let d := psi s k (succ a)
  let f := indexIterFrom s r (succ p)
  have hreg := regularIndex_regular s k (Or.inr ⟨succ r, b, rfl⟩)
  have hsk : succ p < k := regular_succ_lt hreg (successorIndexBase_lt_index s (succ r) b a)
  have hstep : succ p < I s r (succ p) := succ_lt_I_succ s r p
  have hfixed : I s r (sup f) = sup f := indexIterFrom_sup_fixedpoint s r (succ p) hstep
  have hpM : p < sup f := lt_trans _ _ _ (lt_succ_self p) (indexIterFrom_lt_sup s r _ hstep 0)
  apply le_antisymm
  · apply psi_min
    refine ⟨Or.inl (indexIterFrom_sup_lt_higher_I s r (succ r) (succ b) _ (lt_succ_self r) hreg hsk), ?_⟩
    apply C_succ_successor_index_bound s (succ r) b a _
      (lt_of_le_of_lt (le_add _ _) hpM) (lt_of_le_of_lt (right_le_add _ _) hpM)
    · exact hfixed ▸ I_addPrincipal s r (sup f)
    · intro q hq x hx
      rcases (lt_succ_iff_le q r).mp hq with hq | hq
      · have h := I_lower_rank_closed s q r (sup f) x hq (hfixed.symm ▸ hx)
        rwa [hfixed] at h
      · rw [hq]
        have h := I_strict s r hx
        rwa [hfixed] at h
  · have hrC : C s (succ a) d r := C_seed s _ _ r (lt_trans _ _ _ (lt_succ_self r)
      (lt_of_le_of_lt (rank_le_I s (succ r) b)
        (predecessor_index_lt_psi_of_mem s (succ r) b (succ a) hmem)))
    have hC : ∀ n, C s (succ a) d (f n) := by
      intro n
      induction n with
      | zero => exact successorIndexBase_succ_mem s (succ r) b a hmem ha
      | succ n ih => exact C_index s _ _ r _ hrC ih
    exact (sup_le_iff f d).mpr (fun n => Or.inl (psi_closed s k (succ a) _ (hC n)
      (indexIterFrom_lt_higher_I s r (succ r) (succ b) _ (lt_succ_self r) hsk n)))

theorem successor_rank_successor_index_succ_fundamentalSequence (s : Supply) (r b a : O)
    (hmem : C s (succ a) (psi s (I s (succ r) (succ b)) (succ a)) (I s (succ r) (succ b)))
    (ha : C s a (psi s (I s (succ r) (succ b)) a) a) :
    FundamentalSequence (psi s (I s (succ r) (succ b)) (succ a))
      (indexIterFrom s r (succ (successorIndexBase s (succ r) b a))) := by
  rw [successor_rank_successor_index_succ_eq s r b a hmem ha]
  exact ⟨indexIterFrom_lt_sup s r _ (succ_lt_I_succ s r _),
    fun _ _ h => indexIterFrom_strict s r _ (succ_lt_I_succ s r _) h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

theorem rankSuccSup_lt_successor_index_of_lt (s : Supply) (r b c : O)
    (hc : c < I s r (succ b)) : rankSuccSup s r c < I s r (succ b) := by
  have hreg := regularIndex_regular s _ (Or.inr ⟨r, b, rfl⟩)
  have hrk := lt_of_le_of_lt (rank_le_I s r b) (I_strict s r (lt_succ_self b))
  obtain ⟨bound, hbound, hfb⟩ := hreg.2 r hrk
    (fun i => I s (type ((representative r).below i)) (succ c))
    (fun i => I_lower_rank_closed s _ r (succ b) _ (initial_lt r i) (regular_succ_lt hreg hc))
  exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun i => Or.inl (hfb i))) hbound

theorem limit_rank_successor_index_succ_eq (s : Supply) (r b a : O) (hr : IsLimit r)
    (hmem : C s (succ a) (psi s (I s r (succ b)) (succ a)) (I s r (succ b)))
    (ha : C s a (psi s (I s r (succ b)) a) a) :
    psi s (I s r (succ b)) (succ a) = rankSuccSup s r (successorIndexBase s r b a) := by
  let k := I s r (succ b)
  let p := successorIndexBase s r b a
  let d := psi s k (succ a)
  have hreg := regularIndex_regular s k (Or.inr ⟨r, b, rfl⟩)
  have hpk := successorIndexBase_lt_index s r b a
  have hpM := base_lt_rankSuccSup s r p hr
  apply le_antisymm
  · exact psi_min s k (succ a) _ ⟨Or.inl (rankSuccSup_lt_successor_index_of_lt s r b p hpk),
      C_succ_successor_index_bound s r b a _
        (lt_of_le_of_lt (le_add _ _) hpM) (lt_of_le_of_lt (right_le_add _ _) hpM)
        (rankSuccSup_add_closed s r p hr) (fun q hq x hx => rankSuccSup_I_closed s r q p x hr hq hx)⟩
  · have hrlt : r < d := lt_of_le_of_lt (rank_le_I s r b)
      (predecessor_index_lt_psi_of_mem s r b (succ a) hmem)
    apply indexedSup_le
    intro q hq
    exact Or.inl (psi_closed s k (succ a) _ (C_index s _ _ q (succ p)
      (C_seed s _ _ q (lt_trans _ _ _ hq hrlt)) (successorIndexBase_succ_mem s r b a hmem ha))
      (I_lower_rank_closed s q r (succ b) _ hq (regular_succ_lt hreg hpk)))

theorem limit_rank_successor_index_succ_transfiniteFundamentalSequence (s : Supply) (r b a length : O)
    (hmem : C s (succ a) (psi s (I s r (succ b)) (succ a)) (I s r (succ b)))
    (ha : C s a (psi s (I s r (succ b)) a) a)
    (hl : 0 < length) (f : O → O) (hf : TransfiniteFundamentalSequence r length f) :
    TransfiniteFundamentalSequence (psi s (I s r (succ b)) (succ a)) length
      (fun i => I s (f i) (succ (successorIndexBase s r b a))) := by
  have hr := hf.isLimit hl
  rw [limit_rank_successor_index_succ_eq s r b a hr hmem ha]
  refine ⟨fun i hi => I_succ_lt_rankSuccSup s r _ _ hr (hf.below i hi),
    fun i j hij hj => I_succ_rank_strict s _ (hf.strict i j hij hj), ?_⟩
  intro x hx
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q (succ (successorIndexBase s r b a))) x).mp hx
  obtain ⟨i, hi, hqi⟩ := hf.cofinal q hqr
  exact ⟨i, hi, lt_trans _ _ _ hxq (I_succ_rank_strict s _ hqi)⟩

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem successorIndexBase_represented (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a) :
    Represented s (OCF.Denis.successorIndexBase s r b a) :=
  represented_add s _ _ (represented_I s r b hr hb)
    (represented_psi_of_mem s _ a (represented_I s r (succ b) hr (represented_succ s b hb))
      ha (Or.inr ⟨r, b, rfl⟩) harg)

theorem rank_zero_successor_index_succ_dense (s : OCF.Denis.Supply) (b a : OCF.Denis.O)
    (hb : Represented s b) (ha : Represented s a)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s 0 (succ b)) (succ a))
      (OCF.Denis.I s 0 (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 (succ b)) a) a) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 (succ b)) (succ a)) :=
  dense_of_normal_sequence s _ _ (OCF.Denis.rank_zero_successor_index_succ_fundamentalSequence s b a hmem harg)
    (repeatAdd_represented s _ (successorIndexBase_represented s 0 b a ⟨.zero, .zero, rfl⟩ hb ha harg))

theorem successor_rank_successor_index_succ_dense (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s (succ r) (succ b)) (succ a))
      (OCF.Denis.I s (succ r) (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s (succ r) (succ b)) a) a) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) (succ b)) (succ a)) :=
  dense_of_normal_sequence s _ _
    (OCF.Denis.successor_rank_successor_index_succ_fundamentalSequence s r b a hmem harg)
    (indexIterFrom_represented s r _ hr (represented_succ s _
      (successorIndexBase_represented s (succ r) b a (represented_succ s r hr) hb ha harg)))

theorem limit_rank_successor_index_succ_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r b a length : OCF.Denis.O) (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a))
      (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a)
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s r length f) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.successorIndexBase s r b a))) :=
  ⟨OCF.Denis.limit_rank_successor_index_succ_transfiniteFundamentalSequence s r b a length hmem harg hl f hf.fundamental,
    fun i hi hn => represented_I s _ _ (hf.normal i hi hn) (represented_succ s _
      (successorIndexBase_represented s r b a hr hb ha harg))⟩

/-- A successor index whose zero collapse has uncountable cofinality.
The index-membership condition is proved from its normal parameters. -/
theorem uncountable_rank_successor_index_zero_normalFundamentalSequence (s : OCF.Denis.Supply) :
    NormalFundamentalSequence s
      (OCF.Denis.psi s (OCF.Denis.I s (OCF.Denis.I s 0 0) (succ 0)) 0) (OCF.Denis.I s 0 0)
      (fun i => OCF.Denis.I s i (succ (OCF.Denis.I s (OCF.Denis.I s 0 0) 0))) :=
  limit_rank_successor_index_zero_normalFundamentalSequence s _ 0 _
    ⟨omega1, omega1_isNormal s, rfl⟩ ⟨.zero, .zero, rfl⟩
    (OCF.Denis.C_successor_index_of_small_parameter s _ 0 0
      (normal_rankBounded s omega1 (omega1_isNormal s)) (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (OCF.Denis.regular_pos (OCF.Denis.first_regular s)) (fun i => i)
    (regular_normalFundamentalSequence s _ (OCF.Denis.first_regular s))

theorem uncountable_rank_successor_index_zero_cofinality (s : OCF.Denis.Supply) :
    OCF.Denis.cofinality (OCF.Denis.psi s (OCF.Denis.I s (OCF.Denis.I s 0 0) (succ 0)) 0)
      ((uncountable_rank_successor_index_zero_normalFundamentalSequence s).fundamental.isLimit
        (OCF.Denis.regular_pos (OCF.Denis.first_regular s))) = OCF.Denis.I s 0 0 :=
  (OCF.Denis.cofinality_eq_of_transfiniteFundamentalSequence
    (uncountable_rank_successor_index_zero_normalFundamentalSequence s).fundamental
    (OCF.Denis.regular_pos (OCF.Denis.first_regular s))).trans
      (OCF.Denis.cofinality_regular _ (OCF.Denis.first_regular s))

end
end T.Correspondence.Denis.Covering
