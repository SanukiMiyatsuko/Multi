import Multi.term3.Denis.LimitRankSequences

/-! Successor-index branches. The index-membership premise is explicit:
normality of the collapse argument alone does not imply it. -/

namespace OCF.Denis
open Ordinal
noncomputable section

/-- No I-value of the same or a higher rank lies strictly between
I(r,b) and the next r-inaccessible. Limit I-values are included. -/
theorem I_successor_gap (s : Supply) (r b q c : O) (hrq : r ≤ q)
    (h : I s q c < I s r (succ b)) : I s q c ≤ I s r b := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    classical
    have regular_case (x : O) (hx : Inaccessible q x) (hxk : x < I s r (succ b)) : x ≤ I s r b := by
      apply (not_lt_iff_le _ _).mp
      intro hlx
      have hnext := next_le s r (I s r b) x hlx (inaccessible_down hrq hx)
      rw [← I_succ] at hnext
      exact lt_irrefl _ (lt_of_lt_of_le hxk hnext)
    by_cases hz : c = 0
    · subst c
      apply regular_case _ _ h
      rw [I_zero]
      exact first_spec s q
    by_cases hs : ∃ d, c = succ d
    · obtain ⟨d, rfl⟩ := hs
      apply regular_case _ _ h
      rw [I_succ]
      exact (next_spec s q _).2
    · rw [I_limit s q c hz hs]
      exact (sup_le_iff _ _).mpr (fun i => ih _ (initial_lt c i)
        (lt_trans _ _ _ (I_strict s q (initial_lt c i)) h))

theorem C_predecessor_index (s : Supply) (cutoff seed r b : O)
    (h : C s cutoff seed (I s r (succ b))) : C s cutoff seed (I s r b) := by
  have hr : r < I s r (succ b) := lt_of_le_of_lt (rank_le_I s r b) (I_strict s r (lt_succ_self b))
  obtain ⟨hrC, hbC⟩ := C_normal_index_parameters s cutoff seed r (succ b) hr (succ_lt_I_succ s r b) h
  exact C_index s cutoff seed r b hrC (C_predecessor s cutoff seed b hbC)

theorem predecessor_index_lt_psi_of_mem (s : Supply) (r b a : O)
    (h : C s a (psi s (I s r (succ b)) a) (I s r (succ b))) :
    I s r b < psi s (I s r (succ b)) a :=
  psi_closed s _ a _ (C_predecessor_index s a _ r b h) (I_strict s r (lt_succ_self b))

theorem C_successor_index_iff (s : Supply) (r b a : O) :
    C s a (psi s (I s r (succ b)) a) (I s r (succ b)) ↔
      I s r b < psi s (I s r (succ b)) a := by
  refine ⟨predecessor_index_lt_psi_of_mem s r b a, ?_⟩
  intro h
  have hr := lt_of_le_of_lt (rank_le_I s r b) h
  have hb := lt_of_le_of_lt (index_le_I s r b) h
  have hone : succ 0 < psi s (I s r (succ b)) a :=
    lt_trans _ _ _ (lt_of_lt_of_le (lt_trans _ _ _ (finite_lt_omega 1) (first_regular s).1)
      (I_lower_bound s r b)) h
  have hs := C_add s a _ b (succ 0) (C_seed s a _ b hb) (C_seed s a _ _ hone)
  rw [add_succ, add_zero] at hs
  exact C_index s a _ r (succ b) (C_seed s a _ r hr) hs

/-- Failure of index membership puts the value on an earlier plateau.
The earlier I-value need not be a regular index. -/
theorem psi_successor_index_plateau_of_not_mem (s : Supply) (r b a : O)
    (h : ¬ C s a (psi s (I s r (succ b)) a) (I s r (succ b))) :
    psi s (I s r b) a = psi s (I s r (succ b)) a := by
  have hb := (not_lt_iff_le _ _).mp (fun hh => h ((C_successor_index_iff s r b a).mpr hh))
  exact psi_index_plateau s _ _ a hb (Or.inl (I_strict s r (lt_succ_self b)))

theorem first_le_psi_successor_index (s : Supply) (r b a : O) :
    I s 0 0 ≤ psi s (I s r (succ b)) a := by
  apply (not_lt_iff_le _ _).mp
  intro h
  have heq := index_eq_first_of_psi_lt_first s _ a (Or.inr ⟨r, b, rfl⟩) h
  have hlarge := lt_of_le_of_lt (I_lower_bound s r b) (I_strict s r (lt_succ_self b))
  rw [heq] at hlarge
  exact lt_irrefl _ hlarge

/-- Small parameters discharge the index premise; this
uses no assumed hereditary closure for an arbitrary presentation. -/
theorem C_successor_index_of_small_parameters (s : Supply) (r b a : O)
    (hr : r < I s 0 0) (hb : b < I s 0 0) :
    C s a (psi s (I s r (succ b)) a) (I s r (succ b)) :=
  C_index s a _ r (succ b)
    (C_seed s a _ r (lt_of_lt_of_le hr (first_le_psi_successor_index s r b a)))
    (C_seed s a _ _ (lt_of_lt_of_le (regular_succ_lt (first_regular s) hb)
      (first_le_psi_successor_index s r b a)))

theorem C_zero_successor_index_bound (s : Supply) (r b d : O)
    (hbase : I s r b < d) (hadd : AddPrincipal d)
    (hI : ∀ q, q < r → ∀ x, x < d → I s q x < d)
    (x : O) (hx : C s 0 d x) (hbound : x < I s r (succ b)) : x < d := by
  have h := (C_iff s 0 d x).mp hx
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
  | collapse hb _ _ _ _ _ => exact False.elim (not_lt_zero _ hb)

theorem rank_zero_successor_index_zero_eq (s : Supply) (b : O)
    (hmem : C s 0 (psi s (I s 0 (succ b)) 0) (I s 0 (succ b))) :
    psi s (I s 0 (succ b)) 0 = sup (repeatAdd (I s 0 b)) := by
  let k := I s 0 (succ b)
  let p := I s 0 b
  let d := psi s k 0
  have hreg := regularIndex_regular s k (Or.inr ⟨0, b, rfl⟩)
  have hp : 0 < p := lt_of_lt_of_le (regular_pos (first_regular s)) (I_lower_bound s 0 b)
  have hpk : p < k := I_strict s 0 (lt_succ_self b)
  have hpC : C s 0 d p := C_predecessor_index s 0 d 0 b hmem
  apply le_antisymm
  · apply psi_min
    refine ⟨Or.inl (repeatAdd_sup_lt_regular p k hreg hpk), ?_⟩
    apply C_zero_successor_index_bound s 0 b _
    · simpa only [repeatAdd, add_zero] using repeatAdd_lt_sup p hp 1
    · exact repeatAdd_sup_addPrincipal p
    · exact fun q hq => False.elim (not_lt_zero q hq)
  · have hC : ∀ n, C s 0 d (repeatAdd p n) := by
      intro n
      induction n with
      | zero => exact C_zero s 0 d
      | succ n ih => exact C_add s 0 d p _ hpC ih
    exact (sup_le_iff _ d).mpr (fun n => Or.inl
      (psi_closed s k 0 _ (hC n) (repeatAdd_lt_regular p k hreg hpk n)))

theorem rank_zero_successor_index_zero_fundamentalSequence (s : Supply) (b : O)
    (hmem : C s 0 (psi s (I s 0 (succ b)) 0) (I s 0 (succ b))) :
    FundamentalSequence (psi s (I s 0 (succ b)) 0) (repeatAdd (I s 0 b)) := by
  rw [rank_zero_successor_index_zero_eq s b hmem]
  have hp : 0 < I s 0 b := lt_of_lt_of_le (regular_pos (first_regular s)) (I_lower_bound s 0 b)
  exact ⟨repeatAdd_lt_sup _ hp, fun _ _ h => repeatAdd_strict _ hp h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

theorem C_successor_predecessor_index (s : Supply) (r b a : O)
    (hmem : C s a (psi s (I s r (succ b)) a) (I s r (succ b))) :
    C s a (psi s (I s r (succ b)) a) (succ (I s r b)) := by
  have hbase := predecessor_index_lt_psi_of_mem s r b a hmem
  have hone : succ 0 < psi s (I s r (succ b)) a :=
    lt_trans _ _ _ (lt_of_lt_of_le (lt_trans _ _ _ (finite_lt_omega 1) (first_regular s).1)
      (I_lower_bound s r b)) hbase
  have h := C_add s a _ (I s r b) (succ 0) (C_predecessor_index s a _ r b hmem)
    (C_seed s a _ _ hone)
  rwa [add_succ, add_zero] at h

theorem indexIterFrom_lt_higher_I (s : Supply) (q r b c : O) (hqr : q < r)
    (hc : c < I s r b) (n : Nat) : indexIterFrom s q c n < I s r b := by
  induction n with
  | zero => exact hc
  | succ n ih => exact I_lower_rank_closed s q r b _ hqr ih

theorem indexIterFrom_sup_lt_higher_I (s : Supply) (q r b c : O) (hqr : q < r)
    (hreg : UncountableRegular (I s r b)) (hc : c < I s r b) :
    sup (indexIterFrom s q c) < I s r b := by
  obtain ⟨d, hd, hfd⟩ := small_nat hreg (indexIterFrom s q c)
    (indexIterFrom_lt_higher_I s q r b c hqr hc)
  exact lt_of_le_of_lt ((sup_le_iff _ d).mpr (fun n => Or.inl (hfd n))) hd

theorem successor_rank_successor_index_zero_eq (s : Supply) (r b : O)
    (hmem : C s 0 (psi s (I s (succ r) (succ b)) 0) (I s (succ r) (succ b))) :
    psi s (I s (succ r) (succ b)) 0 = sup (indexIterFrom s r (succ (I s (succ r) b))) := by
  let k := I s (succ r) (succ b)
  let p := I s (succ r) b
  let d := psi s k 0
  let f := indexIterFrom s r (succ p)
  have hreg := regularIndex_regular s k (Or.inr ⟨succ r, b, rfl⟩)
  have hpk : p < k := I_strict s (succ r) (lt_succ_self b)
  have hsk : succ p < k := regular_succ_lt hreg hpk
  have hstep : succ p < I s r (succ p) := succ_lt_I_succ s r p
  have hfixed : I s r (sup f) = sup f := indexIterFrom_sup_fixedpoint s r (succ p) hstep
  have hpM : p < sup f := lt_trans _ _ _ (lt_succ_self p) (indexIterFrom_lt_sup s r _ hstep 0)
  apply le_antisymm
  · apply psi_min
    refine ⟨Or.inl (indexIterFrom_sup_lt_higher_I s r (succ r) (succ b) _ (lt_succ_self r) hreg hsk), ?_⟩
    apply C_zero_successor_index_bound s (succ r) b _ hpM
    · exact hfixed ▸ I_addPrincipal s r (sup f)
    · intro q hq x hx
      rcases (lt_succ_iff_le q r).mp hq with hq | hq
      · have h := I_lower_rank_closed s q r (sup f) x hq (hfixed.symm ▸ hx)
        rwa [hfixed] at h
      · rw [hq]
        have h := I_strict s r hx
        rwa [hfixed] at h
  · have hpd : p < d := predecessor_index_lt_psi_of_mem s (succ r) b 0 hmem
    have hrC : C s 0 d r := C_seed s 0 d r (lt_trans _ _ _ (lt_succ_self r)
      (lt_of_le_of_lt (rank_le_I s (succ r) b) hpd))
    have hC : ∀ n, C s 0 d (f n) := by
      intro n
      induction n with
      | zero => exact C_successor_predecessor_index s (succ r) b 0 hmem
      | succ n ih => exact C_index s 0 d r _ hrC ih
    exact (sup_le_iff f d).mpr (fun n => Or.inl (psi_closed s k 0 _ (hC n)
      (indexIterFrom_lt_higher_I s r (succ r) (succ b) _ (lt_succ_self r) hsk n)))

theorem successor_rank_successor_index_zero_fundamentalSequence (s : Supply) (r b : O)
    (hmem : C s 0 (psi s (I s (succ r) (succ b)) 0) (I s (succ r) (succ b))) :
    FundamentalSequence (psi s (I s (succ r) (succ b)) 0)
      (indexIterFrom s r (succ (I s (succ r) b))) := by
  rw [successor_rank_successor_index_zero_eq s r b hmem]
  exact ⟨indexIterFrom_lt_sup s r _ (succ_lt_I_succ s r _),
    fun _ _ h => indexIterFrom_strict s r _ (succ_lt_I_succ s r _) h,
    fun x hx => (lt_sup_iff _ x).mp hx⟩

theorem rankSuccSup_lt_successor_index (s : Supply) (r b : O) :
    rankSuccSup s r (I s r b) < I s r (succ b) := by
  have hreg := regularIndex_regular s _ (Or.inr ⟨r, b, rfl⟩)
  have hpk := I_strict s r (lt_succ_self b)
  have hrk := lt_of_le_of_lt (rank_le_I s r b) hpk
  obtain ⟨bound, hbound, hfb⟩ := hreg.2 r hrk
    (fun i => I s (type ((representative r).below i)) (succ (I s r b)))
    (fun i => I_lower_rank_closed s _ r (succ b) _ (initial_lt r i) (regular_succ_lt hreg hpk))
  exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun i => Or.inl (hfb i))) hbound

theorem limit_rank_successor_index_zero_eq (s : Supply) (r b : O) (hr : IsLimit r)
    (hmem : C s 0 (psi s (I s r (succ b)) 0) (I s r (succ b))) :
    psi s (I s r (succ b)) 0 = rankSuccSup s r (I s r b) := by
  let k := I s r (succ b)
  let p := I s r b
  let d := psi s k 0
  have hreg := regularIndex_regular s k (Or.inr ⟨r, b, rfl⟩)
  have hpk : p < k := I_strict s r (lt_succ_self b)
  apply le_antisymm
  · exact psi_min s k 0 _ ⟨Or.inl (rankSuccSup_lt_successor_index s r b),
      C_zero_successor_index_bound s r b _ (base_lt_rankSuccSup s r p hr)
        (rankSuccSup_add_closed s r p hr) (fun q hq x hx => rankSuccSup_I_closed s r q p x hr hq hx)⟩
  · have hpd := predecessor_index_lt_psi_of_mem s r b 0 hmem
    have hrlt : r < d := lt_of_le_of_lt (rank_le_I s r b) hpd
    have hsC := C_successor_predecessor_index s r b 0 hmem
    apply indexedSup_le
    intro q hq
    exact Or.inl (psi_closed s k 0 _ (C_index s 0 d q (succ p)
      (C_seed s 0 d q (lt_trans _ _ _ hq hrlt)) hsC)
      (I_lower_rank_closed s q r (succ b) _ hq (regular_succ_lt hreg hpk)))

theorem limit_rank_successor_index_zero_transfiniteFundamentalSequence (s : Supply) (r b length : O)
    (hmem : C s 0 (psi s (I s r (succ b)) 0) (I s r (succ b)))
    (hl : 0 < length) (f : O → O) (hf : TransfiniteFundamentalSequence r length f) :
    TransfiniteFundamentalSequence (psi s (I s r (succ b)) 0) length
      (fun i => I s (f i) (succ (I s r b))) := by
  have hr := hf.isLimit hl
  rw [limit_rank_successor_index_zero_eq s r b hr hmem]
  refine ⟨fun i hi => I_succ_lt_rankSuccSup s r _ _ hr (hf.below i hi),
    fun i j hij hj => I_succ_rank_strict s _ (hf.strict i j hij hj), ?_⟩
  intro x hx
  obtain ⟨q, hqr, hxq⟩ := (lt_indexedSup_iff r (fun q => I s q (succ (I s r b))) x).mp hx
  obtain ⟨i, hi, hqi⟩ := hf.cofinal q hqr
  exact ⟨i, hi, lt_trans _ _ _ hxq (I_succ_rank_strict s _ hqi)⟩

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem rank_zero_successor_index_zero_dense (s : OCF.Denis.Supply) (b : OCF.Denis.O)
    (hb : Represented s b)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s 0 (succ b)) 0) (OCF.Denis.I s 0 (succ b))) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 (succ b)) 0) :=
  dense_of_normal_sequence s _ _ (OCF.Denis.rank_zero_successor_index_zero_fundamentalSequence s b hmem)
    (repeatAdd_represented s _ (represented_I s 0 b ⟨.zero, .zero, rfl⟩ hb))

theorem successor_rank_successor_index_zero_dense (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s (succ r) (succ b)) 0)
      (OCF.Denis.I s (succ r) (succ b))) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) (succ b)) 0) :=
  dense_of_normal_sequence s _ _ (OCF.Denis.successor_rank_successor_index_zero_fundamentalSequence s r b hmem)
    (indexIterFrom_represented s r _ hr
      (represented_succ s _ (represented_I s (succ r) b (represented_succ s r hr) hb)))

theorem limit_rank_successor_index_zero_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r b length : OCF.Denis.O) (hr : Represented s r) (hb : Represented s b)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b)))
    (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s r length f) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) length
      (fun i => OCF.Denis.I s (f i) (succ (OCF.Denis.I s r b))) :=
  ⟨OCF.Denis.limit_rank_successor_index_zero_transfiniteFundamentalSequence s r b length hmem hl f hf.fundamental,
    fun i hi hn => represented_I s _ _ (hf.normal i hi hn) (represented_succ s _ (represented_I s r b hr hb))⟩

end
end T.Correspondence.Denis.Covering
