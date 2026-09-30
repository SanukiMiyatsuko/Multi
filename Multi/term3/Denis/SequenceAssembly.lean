import Multi.term3.Denis.StagedCompositeSequences

/-! Assemble minimal-length normal fundamental sequences. These lemmas
retain both the actual ordinal cofinality and representability of the
domain. The final syntactic family records exactly which collapse
branches have been discharged; it does not replace IsNormal. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def HasNormalSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  ∀ ha : OCF.Denis.IsLimit a, Represented s (OCF.Denis.cofinality a ha) ∧
    ∃ f, NormalFundamentalSequence s a (OCF.Denis.cofinality a ha) f

theorem omega_represented (s : OCF.Denis.Supply) : Represented s OCF.Denis.omega :=
  ⟨exp one, tower_isNormal s 2, denote_omega s⟩

theorem hasNormalSequence_of_minimal (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (hb : OCF.Denis.IsLimit b) (hrep : Represented s (OCF.Denis.cofinality b hb))
    (f : OCF.Denis.O → OCF.Denis.O)
    (hf : NormalFundamentalSequence s a (OCF.Denis.cofinality b hb) f) : HasNormalSequence s a := by
  intro ha
  have heq : OCF.Denis.cofinality a ha = OCF.Denis.cofinality b hb := hf.minimal hb
  rw [heq]
  exact ⟨hrep, f, hf⟩

theorem hasNormalSequence_of_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hd : DenseBelow s a) : HasNormalSequence s a := by
  intro ha
  rw [revised_cofinality s a ha hd]
  exact ⟨omega_represented s, _, revised_normalFundamentalSequence s a ha hd⟩

theorem hasNormalSequence_regular (s : OCF.Denis.Supply) (k : OCF.Denis.O)
    (hk : OCF.Denis.UncountableRegular k) (hrep : Represented s k) : HasNormalSequence s k := by
  intro ha
  rw [OCF.Denis.cofinality_regular k hk]
  exact ⟨hrep, _, regular_normalFundamentalSequence s k hk⟩

theorem hasNormalSequence_regular_argument (s : OCF.Denis.Supply) (k r : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hr : OCF.Denis.RegularIndex s r)
    (hkRep : Represented s k) (hrRep : Represented s r) (hkr : k ≤ r)
    (hK : OCF.Denis.C s r (OCF.Denis.psi s k r) k)
    (hR : OCF.Denis.C s r (OCF.Denis.psi s k r) r) :
    HasNormalSequence s (OCF.Denis.psi s k r) :=
  hasNormalSequence_of_dense s _ (proper_regular_argument_dense s k r hk hr hkRep hrRep hkr hK hR)

theorem hasNormalSequence_proper_regular_argument (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.UncountableRegular (denote s a))
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)) :
    HasNormalSequence s (denote s (.psi k a)) := by
  classical
  by_cases hbound : denote s a < denote s k
  · obtain ⟨c, _, _, hf⟩ := proper_regular_below_normalFundamentalSequence s k a hn ha hbound hK
    have hlim := OCF.Denis.regular_isLimit ha
    cases hn with
    | collapse hk haN hreg harg =>
      apply hasNormalSequence_of_minimal s _ _ hlim
      · rw [OCF.Denis.cofinality_regular _ ha]
        exact ⟨a, haN, rfl⟩
      · simpa only [OCF.Denis.cofinality_regular _ ha] using hf
  · cases hn with
    | collapse hk haN hreg harg =>
      exact hasNormalSequence_regular_argument s _ _ hreg (normal_regularIndex s a haN ha)
        ⟨k, hk, rfl⟩ ⟨a, haN, rfl⟩ ((not_lt_iff_le _ _).mp hbound) hK harg

theorem hasNormalSequence_zero (s : OCF.Denis.Supply) : HasNormalSequence s 0 :=
  fun ha => False.elim (ha.1 rfl)

theorem hasNormalSequence_succ (s : OCF.Denis.Supply) (a : OCF.Denis.O) : HasNormalSequence s (succ a) :=
  fun ha => False.elim (ha.2 ⟨a, rfl⟩)

theorem hasNormalSequence_add (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (ha : Represented s a) (hb : b ≠ 0) (hseq : HasNormalSequence s b) : HasNormalSequence s (a + b) := by
  intro hlim
  have hblim := OCF.Denis.right_isLimit_of_add_isLimit a b hb hlim
  obtain ⟨hrep, f, hf⟩ := hseq hblim
  exact hasNormalSequence_of_minimal s (a + b) b hblim hrep _
    (add_normalFundamentalSequence s a b _ ha
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality b hblim)) f hf) hlim

theorem hasNormalSequence_I (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (hseq : HasNormalSequence s b) :
    HasNormalSequence s (OCF.Denis.I s r b) := by
  classical
  have hrep := represented_I s r b hr hb
  by_cases hz : b = 0
  · subst b
    exact hasNormalSequence_regular s _
      (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨r, rfl⟩)) hrep
  by_cases hs : ∃ c, b = succ c
  · obtain ⟨c, rfl⟩ := hs
    exact hasNormalSequence_regular s _
      (OCF.Denis.regularIndex_regular s _ (Or.inr ⟨r, c, rfl⟩)) hrep
  · have hblim : OCF.Denis.IsLimit b := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hseq hblim
    exact hasNormalSequence_of_minimal s _ b hblim hlen _
      (I_normalFundamentalSequence s r b _ hr
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality b hblim)) f hf)

theorem hasNormalSequence_first_collapse (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s a) (hseq : HasNormalSequence s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s 0 0) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s 0 0) a) := by
  classical
  by_cases hz : a = 0
  · subst a
    rw [OCF.Denis.psi_first_zero]
    exact hasNormalSequence_succ s 0
  by_cases hs : ∃ b, a = succ b
  · obtain ⟨b, rfl⟩ := hs
    exact hasNormalSequence_of_dense s _ (psi_first_normal_successor_dense s b ha harg)
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hseq halim
    apply hasNormalSequence_of_minimal s _ a halim hlen _
    apply psi_normalFundamentalSequence s _ a _ ⟨omega1, omega1_isNormal s, rfl⟩ (Or.inl ⟨0, rfl⟩)
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf
    · exact fun _ _ => OCF.Denis.first_mem_C s _ _
    · intro i hi
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f i)
        (hbound halim) harg (hf.fundamental.below i hi))

theorem hasNormalSequence_successor_rank_collapse (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a) (hseq : HasNormalSequence s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s (succ r) 0) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) := by
  classical
  by_cases hz : a = 0
  · subst a
    exact hasNormalSequence_of_dense s _ (successor_rank_zero_dense s r hr)
  by_cases hs : ∃ b, a = succ b
  · obtain ⟨b, rfl⟩ := hs
    exact hasNormalSequence_of_dense s _ (successor_rank_normal_succ_dense s r b hr ha harg)
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hseq halim
    exact hasNormalSequence_of_minimal s _ a halim hlen _
      (successor_rank_limit_normalFundamentalSequence s r a _ hr
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim))
        f hf (hbound halim) harg)

theorem hasNormalSequence_first_index_collapse (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a)
    (hrseq : HasNormalSequence s r) (haseq : HasNormalSequence s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r 0) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s r 0) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) a) := by
  classical
  by_cases hrz : r = 0
  · subst r
    exact hasNormalSequence_first_collapse s a ha haseq harg hbound
  by_cases hrs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hrs
    exact hasNormalSequence_successor_rank_collapse s q a
      (represented_predecessor s q hr) ha haseq harg hbound
  · have hrlim : OCF.Denis.IsLimit r := ⟨hrz, hrs⟩
    have hrank : OCF.Denis.RankBounded s r := by
      obtain ⟨rt, hrt, rfl⟩ := hr
      exact normal_rankBounded s rt hrt
    by_cases haz : a = 0
    · subst a
      obtain ⟨hlen, f, hf⟩ := hrseq hrlim
      exact hasNormalSequence_of_minimal s _ r hrlim hlen _
        (limit_rank_zero_normalFundamentalSequence s r _ hr
          (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)
    by_cases has : ∃ b, a = succ b
    · obtain ⟨b, rfl⟩ := has
      obtain ⟨hlen, f, hf⟩ := hrseq hrlim
      exact hasNormalSequence_of_minimal s _ r hrlim hlen _
        (limit_rank_succ_normalFundamentalSequence s r b _ hr (represented_predecessor s b ha)
          (OCF.Denis.psi_predecessor_argument_normal_general s _ b harg)
          (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)
    · have halim : OCF.Denis.IsLimit a := ⟨haz, has⟩
      obtain ⟨hlen, f, hf⟩ := haseq halim
      apply hasNormalSequence_of_minimal s _ a halim hlen _
      apply psi_normalFundamentalSequence s _ a _ (represented_I s r 0 hr ⟨.zero, .zero, rfl⟩)
        (Or.inl ⟨r, rfl⟩)
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf
      · exact fun _ _ => OCF.Denis.first_rank_index_mem s r _ hrank
      · intro i hi
        exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f i)
          (hbound halim) harg (hf.fundamental.below i hi))

theorem hasNormalSequence_successor_index_zero (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (hrseq : HasNormalSequence s r)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b))) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) := by
  classical
  by_cases hz : r = 0
  · subst r
    exact hasNormalSequence_of_dense s _ (rank_zero_successor_index_zero_dense s b hb hmem)
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasNormalSequence_of_dense s _ (successor_rank_successor_index_zero_dense s q b
      (represented_predecessor s q hr) hb hmem)
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasNormalSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_successor_index_zero_normalFundamentalSequence s r b _ hr hb hmem
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

theorem hasNormalSequence_successor_index_succ (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s (succ a))
    (hrseq : HasNormalSequence s r)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a))
      (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) (succ a)) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) := by
  classical
  have haRep := represented_predecessor s a ha
  have haC := OCF.Denis.psi_predecessor_argument_normal_general s _ a harg
  by_cases hz : r = 0
  · subst r
    exact hasNormalSequence_of_dense s _ (rank_zero_successor_index_succ_dense s b a hb haRep hmem haC)
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasNormalSequence_of_dense s _ (successor_rank_successor_index_succ_dense s q b a
      (represented_predecessor s q hr) hb haRep hmem haC)
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasNormalSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_successor_index_succ_normalFundamentalSequence s r b a _ hr hb haRep hmem haC
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

/-- Once the index belongs to its zero-argument closure, it belongs
at every later argument. This covers zero, arbitrary successors, and
normal limits below the index, with no extra premise on approximants. -/
theorem hasNormalSequence_successor_index_collapse (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hrseq : HasNormalSequence s r) (haseq : HasNormalSequence s a)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s r (succ b)) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) := by
  classical
  have hindex (c : OCF.Denis.O) :
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) c) (OCF.Denis.I s r (succ b)) :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ 0 c (zero_le c)) _
      (OCF.Denis.C_mono_argument s 0 c _ (zero_le c) _ hmem)
  by_cases hz : a = 0
  · subst a
    exact hasNormalSequence_successor_index_zero s r b hr hb hrseq hmem
  by_cases hs : ∃ c, a = succ c
  · obtain ⟨c, rfl⟩ := hs
    exact hasNormalSequence_successor_index_succ s r b c hr hb ha hrseq (hindex _) harg
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := haseq halim
    apply hasNormalSequence_of_minimal s _ a halim hlen _
    apply psi_normalFundamentalSequence s _ a _
      (represented_I s r (succ b) hr (represented_succ s b hb)) (Or.inr ⟨r, b, rfl⟩)
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf
    · exact fun i _ => hindex (f i)
    · intro i hi
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f i)
        (hbound halim) harg (hf.fundamental.below i hi))

theorem hasNormalSequence_successor_index_small_parameter (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hrseq : HasNormalSequence s r) (haseq : HasNormalSequence s a)
    (hbsmall : b < OCF.Denis.I s 0 0)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s r (succ b)) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) := by
  have hrank : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  exact hasNormalSequence_successor_index_collapse s r b a hr hb ha hrseq haseq
    (OCF.Denis.C_successor_index_of_small_parameter s r b 0 hrank hbsmall) harg hbound

theorem hasNormalSequence_countable_limit_collapse (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k) (ha : OCF.Denis.IsLimit a)
    (hseq : HasNormalSequence s a) (hcof : OCF.Denis.cofinality a ha = OCF.Denis.omega)
    (hbound : a < k) (hindex : OCF.Denis.C s a (OCF.Denis.psi s k a) k)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s k a) a) :
    HasNormalSequence s (OCF.Denis.psi s k a) := by
  obtain ⟨_, f, hf⟩ := hseq ha
  rw [hcof] at hf
  exact hasNormalSequence_of_dense s _
    (psi_normal_countable_limit_dense s k a hk hkRep ha hf.omega_dense hbound hindex harg)

theorem hasNormalSequence_successor_index_limit_tail (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : OCF.Denis.IsLimit a)
    (hseq : HasNormalSequence s a) (hbl : b < OCF.Denis.cofinality a ha)
    (hbound : a < OCF.Denis.I s r (succ b))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a) :
    HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) := by
  obtain ⟨hlen, f, hf⟩ := hseq ha
  exact hasNormalSequence_of_minimal s _ a ha hlen _
    (successor_index_limit_tail_normalFundamentalSequence s r b a _ hr hb
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a ha))
      (OCF.Denis.cofinality_addPrincipal a ha) hbl f hf hbound harg)

theorem hasNormalSequence_sum_argument (s : OCF.Denis.Supply) (k p b : Term)
    (hn : IsNormal s (.psi k (.add p b))) (hb : OCF.Denis.IsLimit (denote s b))
    (hseq : HasNormalSequence s (denote s b))
    (hcof : OCF.Denis.cofinality (denote s b) hb = OCF.Denis.omega)
    (hbound : denote s b < denote s k)
    (hK : OCF.Denis.C s (denote s (.add p b)) (denote s (.psi k (.add p b))) (denote s k)) :
    HasNormalSequence s (denote s (.psi k (.add p b))) := by
  obtain ⟨_, f, hf⟩ := hseq hb
  rw [hcof] at hf
  cases hn with
  | collapse hk ha hreg harg =>
    have hpC := C_normal_sum_head s _ _ p b ha harg
    have hbC := OCF.Denis.C_suffix s _ _ _ (denote s p) (denote s b) harg rfl
    cases ha with
    | sum hp hbN hpp hpv hbpos hhead =>
      exact hasNormalSequence_of_dense s _ (proper_sum_countable_dense s _ _ _ hreg
        ⟨k, hk, rfl⟩ ⟨p, hp, rfl⟩ hb hf.omega_dense
        (OCF.Denis.psi_closed s _ _ _ hbC hbound) hpC hK)

theorem hasNormalSequence_I_argument (s : OCF.Denis.Supply) (k r b : Term)
    (hn : IsNormal s (.psi k (.I r b))) (hb : OCF.Denis.IsLimit (denote s b))
    (hseq : HasNormalSequence s (denote s b))
    (hcof : OCF.Denis.cofinality (denote s b) hb = OCF.Denis.omega)
    (hbound : denote s b < denote s k)
    (hK : OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k)) :
    HasNormalSequence s (denote s (.psi k (.I r b))) := by
  obtain ⟨_, f, hf⟩ := hseq hb
  rw [hcof] at hf
  cases hn with
  | collapse hk ha hreg harg =>
    cases ha with
    | index hr hbN hrl hbl =>
      exact hasNormalSequence_of_dense s _ (proper_normal_I_countable_dense s _ _ _ hreg
        ⟨k, hk, rfl⟩ ⟨r, hr, rfl⟩ hb hf.omega_dense hrl hbl hbound hK harg)

/-- The zero-collapse induction step for every normal regular index.
Only sequences for ranks of I subterms are used; membership of the
displayed index in its closure is proved after a value-preserving
subterm reduction. -/
theorem hasNormalSequence_zero_collapse (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k))
    (hranks : ∀ r b, ZeroIndex.Subterm (.I r b) k → HasNormalSequence s (denote s r)) :
    HasNormalSequence s (OCF.Denis.psi s (denote s k) 0) := by
  obtain ⟨r, b, hs, hn, hr, hmem, heq⟩ := ZeroIndex.exists_normal_index s k hk hreg
  rw [heq]
  have hrseq := hranks r b hs
  cases hn with
  | index hrN hbN hrl hbl =>
    change HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) 0)
    rcases OCF.Denis.regular_I_argument s _ _ hbl (OCF.Denis.regularIndex_regular s _ hr) with hz | hsucc
    · rw [hz]
      exact hasNormalSequence_first_index_collapse s _ 0 ⟨r, hrN, rfl⟩ ⟨.zero, .zero, rfl⟩
        hrseq (hasNormalSequence_zero s) (OCF.Denis.C_zero s 0 _)
        (fun h => False.elim (h.1 rfl))
    · obtain ⟨c, hc⟩ := hsucc
      change OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) 0)
        (OCF.Denis.I s (denote s r) (denote s b)) at hmem
      rw [hc] at hmem ⊢
      exact hasNormalSequence_successor_index_zero s _ c ⟨r, hrN, rfl⟩
        (represented_predecessor s c ⟨b, hbN, hc⟩) hrseq hmem

theorem hasNormalSequence_zero_collapse_induction (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k))
    (ih : ∀ r, sizeOf r < sizeOf k → IsNormal s r → HasNormalSequence s (denote s r)) :
    HasNormalSequence s (OCF.Denis.psi s (denote s k) 0) :=
  hasNormalSequence_zero_collapse s k hk hreg (fun r _ hs => ih r hs.index_rank_size_lt
    ((ZeroIndex.Subterm.indexRank (.refl r)).trans hs |>.normal hk))

/-- A missing index-membership condition is handled by structural
induction for arbitrary arguments, not added as a global assumption. -/
theorem hasNormalSequence_collapse_of_index_not_mem (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a))
    (hnot : ¬ OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k))
    (ih : ∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasNormalSequence s (denote s u)) :
    HasNormalSequence s (denote s (.psi k a)) := by
  obtain ⟨l, b, hb, heq, hsize⟩ := CollapseNormalization.smaller_of_index_not_mem s k a hn hnot
  rw [← heq]
  exact ih (.psi l b) hsize hb

/-- The entire zero/successor-argument collapse clause of a structural
induction. No bound on the argument and no index-membership premise
remain. The general theorem still needs the limit-argument clause. -/
theorem hasNormalSequence_nonlimit_collapse_induction (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (haNonlimit : denote s a = 0 ∨ ∃ c, denote s a = succ c)
    (ih : ∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasNormalSequence s (denote s u)) :
    HasNormalSequence s (denote s (.psi k a)) := by
  classical
  by_cases hmem : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)
  · cases hn with
    | collapse hk ha hreg harg =>
      obtain ⟨r, b, rfl⟩ := CollapseNormalization.normal_regular_is_index s k hk
        (OCF.Denis.regularIndex_regular s _ hreg)
      cases hk with
      | index hr hb hrl hbl =>
        have hrseq := ih r (by simp; omega) hr
        rcases haNonlimit with haz | hasucc
        · change HasNormalSequence s (OCF.Denis.psi s (denote s (.I r b)) (denote s a))
          rw [haz]
          exact hasNormalSequence_zero_collapse s (.I r b) (.index hr hb hrl hbl) hreg
            (fun q c hs => ih q (by have hh := hs.index_rank_size_lt; simp at hh ⊢; omega)
              ((ZeroIndex.Subterm.indexRank (.refl q)).trans hs |>.normal (.index hr hb hrl hbl)))
        · obtain ⟨c, hc⟩ := hasucc
          change HasNormalSequence s (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
          change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
            (denote s a) at harg
          change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
            (OCF.Denis.I s (denote s r) (denote s b)) at hmem
          rw [hc] at harg hmem ⊢
          rcases OCF.Denis.regular_I_argument s _ _ hbl (OCF.Denis.regularIndex_regular s _ hreg) with hbz | hbs
          · rw [hbz] at harg ⊢
            exact hasNormalSequence_first_index_collapse s _ (succ c) ⟨r, hr, rfl⟩ ⟨a, ha, hc⟩
              hrseq (hasNormalSequence_succ s c) harg (fun h => False.elim (h.2 ⟨c, rfl⟩))
          · obtain ⟨d, hd⟩ := hbs
            rw [hd] at harg hmem ⊢
            exact hasNormalSequence_successor_index_succ s _ d c ⟨r, hr, rfl⟩
              (represented_predecessor s d ⟨b, hb, hd⟩) ⟨a, ha, hc⟩ hrseq hmem harg
  · exact hasNormalSequence_collapse_of_index_not_mem s k a hn hmem ih

/-- The remaining induction obligation. This is an explicit proposition,
not an assumed instance or an axiom: it still has to be proved for
proper collapses at limit arguments. -/
def ProperLimitStep (s : OCF.Denis.Supply) : Prop :=
  ∀ r b a, IsNormal s (.psi (.I r b) a) → OCF.Denis.IsLimit (denote s a) →
    OCF.Denis.C s (denote s a) (denote s (.psi (.I r b) a)) (denote s (.I r b)) →
    (∀ u, sizeOf u < sizeOf (Term.psi (.I r b) a) → IsNormal s u → HasNormalSequence s (denote s u)) →
    HasNormalSequence s (denote s (.psi (.I r b) a))

theorem normal_hasNormalSequence_of_proper_limit (s : OCF.Denis.Supply) (hlimit : ProperLimitStep s)
    (t : Term) (ht : IsNormal s t) : HasNormalSequence s (denote s t) := by
  classical
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    cases ht with
    | zero => exact hasNormalSequence_zero s
    | @sum a b ha hb hap hp hbpos hhead =>
      exact hasNormalSequence_add s _ _ ⟨a, ha, rfl⟩ ((zero_lt_iff_ne_zero _).mp hbpos)
        (ih b (by change sizeOf b < sizeOf (Term.add a b); simp; omega) hb)
    | @index r b hr hb hrl hbl =>
      exact hasNormalSequence_I s _ _ ⟨r, hr, rfl⟩ ⟨b, hb, rfl⟩
        (ih b (by change sizeOf b < sizeOf (Term.I r b); simp; omega) hb)
    | @collapse k a hk ha hreg harg =>
      have hn : IsNormal s (.psi k a) := .collapse hk ha hreg harg
      by_cases halim : OCF.Denis.IsLimit (denote s a)
      · by_cases hmem : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)
        · obtain ⟨r, b, rfl⟩ := CollapseNormalization.normal_regular_is_index s k hk
            (OCF.Denis.regularIndex_regular s _ hreg)
          exact hlimit r b a hn halim hmem ih
        · exact hasNormalSequence_collapse_of_index_not_mem s k a hn hmem ih
      · apply hasNormalSequence_nonlimit_collapse_induction s k a hn _ ih
        by_cases hz : denote s a = 0
        · exact Or.inl hz
        by_cases hs : ∃ c, denote s a = succ c
        · exact Or.inr hs
        · exact False.elim (halim ⟨hz, hs⟩)

theorem properLimitStep_iff_all_normal (s : OCF.Denis.Supply) :
    ProperLimitStep s ↔ ∀ t, IsNormal s t → HasNormalSequence s (denote s t) :=
  ⟨fun h => normal_hasNormalSequence_of_proper_limit s h,
    fun h r b a hn _ _ _ => h (.psi (.I r b) a) hn⟩

/-- Uncountable regular arguments have been discharged. This remaining
limit clause includes omega and singular arguments; it is not assumed. -/
def ProperRemainingLimitStep (s : OCF.Denis.Supply) : Prop :=
  ∀ r b a, IsNormal s (.psi (.I r b) a) → OCF.Denis.IsLimit (denote s a) →
    ¬ OCF.Denis.UncountableRegular (denote s a) →
    OCF.Denis.C s (denote s a) (denote s (.psi (.I r b) a)) (denote s (.I r b)) →
    (∀ u, sizeOf u < sizeOf (Term.psi (.I r b) a) → IsNormal s u → HasNormalSequence s (denote s u)) →
    HasNormalSequence s (denote s (.psi (.I r b) a))

theorem properLimitStep_of_remaining (s : OCF.Denis.Supply) (hs : ProperRemainingLimitStep s) :
    ProperLimitStep s := by
  intro r b a hn ha hK ih
  classical
  by_cases hreg : OCF.Denis.UncountableRegular (denote s a)
  · exact hasNormalSequence_proper_regular_argument s (.I r b) a hn hreg hK
  · exact hs r b a hn ha hreg hK ih

theorem properRemainingLimitStep_iff_all_normal (s : OCF.Denis.Supply) :
    ProperRemainingLimitStep s ↔ ∀ t, IsNormal s t → HasNormalSequence s (denote s t) :=
  ⟨fun h => normal_hasNormalSequence_of_proper_limit s (properLimitStep_of_remaining s h),
    fun h r b a hn _ _ _ _ => h (.psi (.I r b) a) hn⟩

/-- A syntactic family whose branches have all been proved. Fixed
summands and ranks may be arbitrary normal terms. Collapse indices can
be any normal presentation with the stated canonical ordinal value. -/
inductive SequenceTerm (s : OCF.Denis.Supply) : Term → Prop where
  | bounded {t : Term} : IsNormal s t →
      denote s t ≤ OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s 0 0) → SequenceTerm s t
  | successor {t : Term} : IsNormal s t → (∃ a, denote s t = succ a) → SequenceTerm s t
  | regular {t : Term} : IsNormal s t → OCF.Denis.UncountableRegular (denote s t) → SequenceTerm s t
  | sum {a b : Term} : SequenceTerm s b → IsNormal s (.add a b) → SequenceTerm s (.add a b)
  | index {r b : Term} : SequenceTerm s b → IsNormal s (.I r b) → SequenceTerm s (.I r b)
  | first {k a : Term} : SequenceTerm s a → IsNormal s (.psi k a) → denote s k = OCF.Denis.I s 0 0 →
      (OCF.Denis.IsLimit (denote s a) → denote s a < OCF.Denis.I s 0 0) → SequenceTerm s (.psi k a)
  | successorRank {k a r : Term} : IsNormal s r → SequenceTerm s a → IsNormal s (.psi k a) →
      denote s k = OCF.Denis.I s (succ (denote s r)) 0 →
      (OCF.Denis.IsLimit (denote s a) → denote s a < denote s k) → SequenceTerm s (.psi k a)
  | firstIndex {k a r : Term} : SequenceTerm s r → SequenceTerm s a → IsNormal s (.psi k a) →
      denote s k = OCF.Denis.I s (denote s r) 0 →
      (OCF.Denis.IsLimit (denote s a) → denote s a < denote s k) → SequenceTerm s (.psi k a)
  | successorIndexZero {k a r b : Term} : SequenceTerm s r → IsNormal s b → IsNormal s (.psi k a) →
      denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)) → denote s a = 0 →
      OCF.Denis.C s 0 (OCF.Denis.psi s (denote s k) 0) (denote s k) → SequenceTerm s (.psi k a)
  | successorIndexSucc {k a r b : Term} : SequenceTerm s r → IsNormal s b → IsNormal s (.psi k a) →
      denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)) → (∃ c, denote s a = succ c) →
      OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a)) (denote s k) →
      SequenceTerm s (.psi k a)
  | successorIndex {k a r b : Term} : SequenceTerm s r → SequenceTerm s a → IsNormal s b →
      IsNormal s (.psi k a) → denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)) →
      OCF.Denis.C s 0 (OCF.Denis.psi s (denote s k) 0) (denote s k) →
      (OCF.Denis.IsLimit (denote s a) → denote s a < denote s k) → SequenceTerm s (.psi k a)
  | countableLimit {k a : Term} : SequenceTerm s a → IsNormal s (.psi k a) →
      (ha : OCF.Denis.IsLimit (denote s a)) → OCF.Denis.cofinality (denote s a) ha = OCF.Denis.omega →
      denote s a < denote s k →
      OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a)) (denote s k) →
      SequenceTerm s (.psi k a)
  | successorIndexLimitTail {k a r b : Term} : SequenceTerm s a → IsNormal s r → IsNormal s b →
      IsNormal s (.psi k a) → denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)) →
      (ha : OCF.Denis.IsLimit (denote s a)) → denote s b < OCF.Denis.cofinality (denote s a) ha →
      denote s a < denote s k → SequenceTerm s (.psi k a)
  | zeroCollapse {k a : Term} :
      (∀ r b, ZeroIndex.Subterm (.I r b) k → SequenceTerm s r) →
      IsNormal s (.psi k a) → denote s a = 0 → SequenceTerm s (.psi k a)
  | regularArgument {k a : Term} : IsNormal s (.psi k a) →
      OCF.Denis.UncountableRegular (denote s a) →
      OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) → SequenceTerm s (.psi k a)
  | countableSumArgument {k p b : Term} : SequenceTerm s b → IsNormal s (.psi k (.add p b)) →
      (hb : OCF.Denis.IsLimit (denote s b)) → OCF.Denis.cofinality (denote s b) hb = OCF.Denis.omega →
      denote s b < denote s k →
      OCF.Denis.C s (denote s (.add p b)) (denote s (.psi k (.add p b))) (denote s k) →
      SequenceTerm s (.psi k (.add p b))
  | countableIndexArgument {k r b : Term} : SequenceTerm s b → IsNormal s (.psi k (.I r b)) →
      (hb : OCF.Denis.IsLimit (denote s b)) → OCF.Denis.cofinality (denote s b) hb = OCF.Denis.omega →
      denote s b < denote s k →
      OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k) →
      SequenceTerm s (.psi k (.I r b))
  | diagonal {k t : Term} : CollapseTree s t → IsNormal s (.psi k t) →
      denote s k = OCF.Denis.I s 0 0 → OCF.Denis.RegularIndex s (denote s t) → SequenceTerm s (.psi k t)
  | equalValue {t u : Term} : SequenceTerm s u → IsNormal s t → denote s t = denote s u → SequenceTerm s t

theorem SequenceTerm.normal {s : OCF.Denis.Supply} {t : Term} (ht : SequenceTerm s t) : IsNormal s t := by
  cases ht <;> assumption

theorem SequenceTerm.normalizedCollapse {s : OCF.Denis.Supply} {t : Term} (ht : IsNormal s t)
    (hc : ∃ k a, t = .psi k a) (hs : SequenceTerm s (CollapseNormalization.normalize s t ht hc)) :
    SequenceTerm s t :=
  .equalValue hs ht (CollapseNormalization.normalize_spec s t ht hc).2.1.symm

theorem SequenceTerm.successorIndexSmallParameter {s : OCF.Denis.Supply} {k a r b : Term}
    (hr : SequenceTerm s r) (ha : SequenceTerm s a) (hb : IsNormal s b) (hn : IsNormal s (.psi k a))
    (heq : denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)))
    (hbsmall : denote s b < OCF.Denis.I s 0 0)
    (hbound : OCF.Denis.IsLimit (denote s a) → denote s a < denote s k) : SequenceTerm s (.psi k a) := by
  apply SequenceTerm.successorIndex hr ha hb hn heq
  · rw [heq]
    exact OCF.Denis.C_successor_index_of_small_parameter s _ _ 0
      (normal_rankBounded s r hr.normal) hbsmall
  · exact hbound

theorem SequenceTerm.successorIndexParameterLeRank {s : OCF.Denis.Supply} {k a r b : Term}
    (hr : SequenceTerm s r) (ha : SequenceTerm s a) (hb : IsNormal s b) (hn : IsNormal s (.psi k a))
    (heq : denote s k = OCF.Denis.I s (denote s r) (succ (denote s b)))
    (hbr : denote s b ≤ denote s r)
    (hbound : OCF.Denis.IsLimit (denote s a) → denote s a < denote s k) : SequenceTerm s (.psi k a) := by
  apply SequenceTerm.successorIndex hr ha hb hn heq
  · rw [heq]
    exact OCF.Denis.C_successor_index_of_parameter_le_rank s _ _ 0
      (normal_rankBounded s r hr.normal) hbr
  · exact hbound

theorem SequenceTerm.hasNormalSequence {s : OCF.Denis.Supply} {t : Term} (ht : SequenceTerm s t) :
    HasNormalSequence s (denote s t) := by
  induction ht with
  | @bounded t ht hbound =>
    intro hlim
    exact hasNormalSequence_of_dense s _ (normal_dense_below_first_diagonal s t ht hbound hlim) hlim
  | successor _ hs =>
    obtain ⟨a, heq⟩ := hs
    rw [heq]
    exact hasNormalSequence_succ s a
  | @regular t ht hreg => exact hasNormalSequence_regular s _ hreg ⟨t, ht, rfl⟩
  | @sum a b hb hn ih =>
    cases hn with
    | sum ha hb hap hp hbpos hhead =>
      exact hasNormalSequence_add s _ _ ⟨a, ha, rfl⟩ ((zero_lt_iff_ne_zero _).mp hbpos) ih
  | @index r b hb hn ih =>
    cases hn with
    | index hr hb hrl hbl => exact hasNormalSequence_I s _ _ ⟨r, hr, rfl⟩ ⟨b, hb, rfl⟩ ih
  | @first k a ha hn heq hbound ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg ⊢
      exact hasNormalSequence_first_collapse s _ ⟨a, ha, rfl⟩ ih harg hbound
  | @successorRank k a r hr ha hn heq hbound ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hbound ⊢
      exact hasNormalSequence_successor_rank_collapse s _ _ ⟨r, hr, rfl⟩ ⟨a, ha, rfl⟩ ih harg hbound
  | @firstIndex k a r hr ha hn heq hbound ihr iha =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hbound ⊢
      exact hasNormalSequence_first_index_collapse s _ _ ⟨r, hr.normal, rfl⟩ ⟨a, ha, rfl⟩ ihr iha harg hbound
  | @successorIndexZero k a r b hr hb hn heq haz hmem ihr =>
    change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
    rw [heq] at hmem
    rw [heq, haz]
    exact hasNormalSequence_successor_index_zero s _ _ ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩ ihr hmem
  | @successorIndexSucc k a r b hr hb hn heq has hmem ihr =>
    cases hn with
    | collapse hk ha hreg harg =>
      obtain ⟨c, hc⟩ := has
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq, hc] at harg hmem ⊢
      exact hasNormalSequence_successor_index_succ s _ _ c ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩
        ⟨a, ha, hc⟩ ihr hmem harg
  | @successorIndex k a r b hr ha hb hn heq hmem hbound ihr iha =>
    cases hn with
    | collapse hk haN hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hmem hbound ⊢
      exact hasNormalSequence_successor_index_collapse s _ _ _ ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩
        ⟨a, haN, rfl⟩ ihr iha hmem harg hbound
  | @countableLimit k a ha hn halim hcof hbound hindex ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      exact hasNormalSequence_countable_limit_collapse s _ _ hreg ⟨k, hk, rfl⟩ halim
        ih hcof hbound hindex harg
  | @successorIndexLimitTail k a r b ha hr hb hn heq halim hbl hbound ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hbound ⊢
      exact hasNormalSequence_successor_index_limit_tail s _ _ _ ⟨r, hr, rfl⟩ ⟨b, hb, rfl⟩
        halim ih hbl hbound harg
  | @zeroCollapse k a hranks hn haz ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [haz]
      exact hasNormalSequence_zero_collapse s k hk hreg ih
  | @regularArgument k a hn hr hK =>
    exact hasNormalSequence_proper_regular_argument s k a hn hr hK
  | @countableSumArgument k p b hb hn hlim hcof hbound hK ih =>
    exact hasNormalSequence_sum_argument s k p b hn hlim ih hcof hbound hK
  | @countableIndexArgument k r b hb hn hlim hcof hbound hK ih =>
    exact hasNormalSequence_I_argument s k r b hn hlim ih hcof hbound hK
  | @diagonal k t ht hn heq hreg =>
    cases hn with
    | collapse hk htN _ harg =>
      change HasNormalSequence s (OCF.Denis.psi s (denote s k) (denote s t))
      rw [heq] at harg ⊢
      exact hasNormalSequence_of_dense s _ (collapseTree_diagonal_dense s t ht hreg harg)
  | equalValue _ _ heq ih => rwa [heq]

theorem SequenceTerm.minimal_normal_sequence {s : OCF.Denis.Supply} {t : Term}
    (ht : SequenceTerm s t) (hlim : OCF.Denis.IsLimit (denote s t)) :
    Represented s (OCF.Denis.cofinality (denote s t) hlim) ∧
      ∃ f, NormalFundamentalSequence s (denote s t) (OCF.Denis.cofinality (denote s t) hlim) f :=
  ht.hasNormalSequence hlim

/-- A single ordinal function selected from the proved family. Its
length is the actual cofinality, not an arbitrarily chosen ordinal. -/
def minimalSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) : OCF.Denis.O → OCF.Denis.O :=
  Classical.choose (hs ha).2

theorem minimalSequence_spec (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) :
    NormalFundamentalSequence s a (OCF.Denis.cofinality a ha) (minimalSequence s a hs ha) :=
  Classical.choose_spec (hs ha).2

def minimalDomainTerm (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) : Term :=
  termOf s ⟨OCF.Denis.cofinality a ha, (hs ha).1⟩

theorem minimalDomainTerm_normal (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) : IsNormal s (minimalDomainTerm s a hs ha) :=
  termOf_normal s _

theorem denote_minimalDomainTerm (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) :
    denote s (minimalDomainTerm s a hs ha) = OCF.Denis.cofinality a ha := denote_termOf s _

def minimalStepTerm (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) (i : Term) (hi : IsNormal s i) : Term :=
  if h : denote s i < OCF.Denis.cofinality a ha then
    termOf s ⟨minimalSequence s a hs ha (denote s i),
      (minimalSequence_spec s a hs ha).normal _ h ⟨i, hi, rfl⟩⟩
  else .zero

theorem minimalStepTerm_normal (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) (i : Term) (hi : IsNormal s i) :
    IsNormal s (minimalStepTerm s a hs ha i hi) := by
  unfold minimalStepTerm
  split
  · exact termOf_normal s _
  · exact .zero

theorem denote_minimalStepTerm (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) (i : Term) (hi : IsNormal s i)
    (hib : denote s i < OCF.Denis.cofinality a ha) :
    denote s (minimalStepTerm s a hs ha i hi) = minimalSequence s a hs ha (denote s i) := by
  unfold minimalStepTerm
  rw [dite_eq_left hib]
  exact denote_termOf s _

theorem minimalStepTerm_below (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) (i : Term) (hi : IsNormal s i)
    (hib : denote s i < OCF.Denis.cofinality a ha) :
    denote s (minimalStepTerm s a hs ha i hi) < a := by
  rw [denote_minimalStepTerm s a hs ha i hi hib]
  exact (minimalSequence_spec s a hs ha).fundamental.below _ hib

theorem minimalStepTerm_strict (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a) (ha : OCF.Denis.IsLimit a) (i j : Term)
    (hi : IsNormal s i) (hj : IsNormal s j)
    (hij : denote s i < denote s j) (hjb : denote s j < OCF.Denis.cofinality a ha) :
    denote s (minimalStepTerm s a hs ha i hi) < denote s (minimalStepTerm s a hs ha j hj) := by
  rw [denote_minimalStepTerm s a hs ha i hi (OCF.Ordinal.lt_trans _ _ _ hij hjb),
    denote_minimalStepTerm s a hs ha j hj hjb]
  exact (minimalSequence_spec s a hs ha).fundamental.strict _ _ hij hjb

theorem SequenceTerm.revised_fundamentalSequence {s : OCF.Denis.Supply} {t : Term}
    (ht : SequenceTerm s t) (hlim : OCF.Denis.IsLimit (denote s t))
    (hcf : OCF.Denis.cofinality (denote s t) hlim = OCF.Denis.omega) :
    OCF.Denis.FundamentalSequence (denote s t) (revisedValue s (denote s t)) := by
  obtain ⟨_, f, hf⟩ := ht.minimal_normal_sequence hlim
  rw [hcf] at hf
  exact revised_fundamentalSequence_of_dense s _ ((zero_lt_iff_ne_zero _).mpr hlim.1) hf.omega_dense

/-- The stronger induction invariant: in addition to actual ordinal
cofinality, represented indices cover every represented bound. -/
def HasCoveringSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  ∀ ha : OCF.Denis.IsLimit a, Represented s (OCF.Denis.cofinality a ha) ∧
    ∃ f, CoveringFundamentalSequence s a (OCF.Denis.cofinality a ha) f

theorem HasCoveringSequence.to_normal {s : OCF.Denis.Supply} {a : OCF.Denis.O}
    (hs : HasCoveringSequence s a) : HasNormalSequence s a := by
  intro ha
  obtain ⟨hlen, f, hf⟩ := hs ha
  exact ⟨hlen, f, hf.normalSequence⟩

theorem hasCoveringSequence_of_minimal (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (hb : OCF.Denis.IsLimit b) (hrep : Represented s (OCF.Denis.cofinality b hb))
    (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s a (OCF.Denis.cofinality b hb) f) : HasCoveringSequence s a := by
  intro ha
  have heq : OCF.Denis.cofinality a ha = OCF.Denis.cofinality b hb := hf.normalSequence.minimal hb
  rw [heq]
  exact ⟨hrep, f, hf⟩

theorem hasCoveringSequence_of_countable (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hs : HasNormalSequence s a)
    (hcof : ∀ ha, OCF.Denis.cofinality a ha = OCF.Denis.omega) : HasCoveringSequence s a := by
  intro ha
  obtain ⟨hlen, f, hf⟩ := hs ha
  rw [hcof ha] at hf ⊢
  exact ⟨omega_represented s, f, coveringFundamentalSequence_of_omega s a f hf⟩

theorem hasCoveringSequence_of_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (hd : DenseBelow s a) : HasCoveringSequence s a :=
  hasCoveringSequence_of_countable s a (hasNormalSequence_of_dense s a hd)
    (fun ha => revised_cofinality s a ha hd)

theorem hasCoveringSequence_regular (s : OCF.Denis.Supply) (k : OCF.Denis.O)
    (hk : OCF.Denis.UncountableRegular k) (hrep : Represented s k) : HasCoveringSequence s k := by
  intro ha
  rw [OCF.Denis.cofinality_regular k hk]
  exact ⟨hrep, _, regular_coveringFundamentalSequence s k hk⟩

theorem hasCoveringSequence_zero (s : OCF.Denis.Supply) : HasCoveringSequence s 0 :=
  fun ha => False.elim (ha.1 rfl)

theorem hasCoveringSequence_succ (s : OCF.Denis.Supply) (a : OCF.Denis.O) : HasCoveringSequence s (succ a) :=
  fun ha => False.elim (ha.2 ⟨a, rfl⟩)

theorem hasCoveringSequence_add (s : OCF.Denis.Supply) (p a : OCF.Denis.O)
    (hp : Represented s p) (ha : a ≠ 0) (hs : HasCoveringSequence s a) : HasCoveringSequence s (p + a) := by
  intro hlim
  have halim := OCF.Denis.right_isLimit_of_add_isLimit p a ha hlim
  obtain ⟨hlen, f, hf⟩ := hs halim
  exact hasCoveringSequence_of_minimal s _ a halim hlen _
    (add_coveringFundamentalSequence s p a _ hp
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf) hlim

theorem hasCoveringSequence_I (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a) (hs : HasCoveringSequence s a) :
    HasCoveringSequence s (OCF.Denis.I s r a) := by
  classical
  have hrep := represented_I s r a hr ha
  by_cases hz : a = 0
  · subst a
    exact hasCoveringSequence_regular s _
      (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨r, rfl⟩)) hrep
  by_cases hsucc : ∃ c, a = succ c
  · obtain ⟨c, rfl⟩ := hsucc
    exact hasCoveringSequence_regular s _
      (OCF.Denis.regularIndex_regular s _ (Or.inr ⟨r, c, rfl⟩)) hrep
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hsucc⟩
    obtain ⟨hlen, f, hf⟩ := hs halim
    exact hasCoveringSequence_of_minimal s _ a halim hlen _
      (I_coveringFundamentalSequence s r a _ hr
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf)

theorem hasCoveringSequence_proper_limit_below (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.IsLimit (denote s a))
    (hs : HasCoveringSequence s (denote s a)) (hbound : denote s a < denote s k)
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)) :
    HasCoveringSequence s (denote s (.psi k a)) := by
  obtain ⟨hlen, f, hf⟩ := hs ha
  obtain ⟨_, _, _, hg⟩ := proper_limit_below_coveringFundamentalSequence s k a hn hbound hK _
    (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality _ ha))
    (OCF.Denis.cofinality_addPrincipal _ ha) f hf
  exact hasCoveringSequence_of_minimal s _ _ ha hlen _ hg

theorem hasCoveringSequence_proper_regular_argument (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (ha : OCF.Denis.UncountableRegular (denote s a))
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)) :
    HasCoveringSequence s (denote s (.psi k a)) := by
  classical
  by_cases hbound : denote s a < denote s k
  · have haN : IsNormal s a := by cases hn; assumption
    exact hasCoveringSequence_proper_limit_below s k a hn (OCF.Denis.regular_isLimit ha)
      (hasCoveringSequence_regular s _ ha ⟨a, haN, rfl⟩) hbound hK
  · cases hn with
    | collapse hk haN hreg harg =>
      exact hasCoveringSequence_of_dense s _ (proper_regular_argument_dense s _ _ hreg
        (normal_regularIndex s a haN ha) ⟨k, hk, rfl⟩ ⟨a, haN, rfl⟩
        ((not_lt_iff_le _ _).mp hbound) hK harg)

theorem hasCoveringSequence_first_index_zero (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) (hrseq : HasCoveringSequence s r) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) 0) := by
  classical
  by_cases hz : r = 0
  · subst r
    rw [OCF.Denis.psi_first_zero]
    exact hasCoveringSequence_succ s 0
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasCoveringSequence_of_dense s _ (successor_rank_zero_dense s q (represented_predecessor s q hr))
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasCoveringSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_zero_coveringFundamentalSequence s r _ hr
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

theorem hasCoveringSequence_first_index_succ (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s (succ a)) (hrseq : HasCoveringSequence s r)
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r 0) (succ a)) (succ a)) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) (succ a)) := by
  classical
  by_cases hz : r = 0
  · subst r
    exact hasCoveringSequence_of_dense s _ (psi_first_normal_successor_dense s a ha harg)
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasCoveringSequence_of_dense s _ (successor_rank_normal_succ_dense s q a
      (represented_predecessor s q hr) ha harg)
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasCoveringSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_succ_coveringFundamentalSequence s r a _ hr (represented_predecessor s a ha)
        (OCF.Denis.psi_predecessor_argument_normal_general s _ a harg)
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

theorem hasCoveringSequence_successor_index_zero (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (hrseq : HasCoveringSequence s r)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b))) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) := by
  classical
  by_cases hz : r = 0
  · subst r
    exact hasCoveringSequence_of_dense s _ (rank_zero_successor_index_zero_dense s b hb hmem)
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasCoveringSequence_of_dense s _ (successor_rank_successor_index_zero_dense s q b
      (represented_predecessor s q hr) hb hmem)
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasCoveringSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_successor_index_zero_coveringFundamentalSequence s r b _ hr hb hmem
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

theorem hasCoveringSequence_successor_index_succ (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s (succ a))
    (hrseq : HasCoveringSequence s r)
    (hmem : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a))
      (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s (succ a) (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) (succ a)) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (succ a)) := by
  classical
  have haRep := represented_predecessor s a ha
  have haC := OCF.Denis.psi_predecessor_argument_normal_general s _ a harg
  by_cases hz : r = 0
  · subst r
    exact hasCoveringSequence_of_dense s _ (rank_zero_successor_index_succ_dense s b a hb haRep hmem haC)
  by_cases hs : ∃ q, r = succ q
  · obtain ⟨q, rfl⟩ := hs
    exact hasCoveringSequence_of_dense s _ (successor_rank_successor_index_succ_dense s q b a
      (represented_predecessor s q hr) hb haRep hmem haC)
  · have hrlim : OCF.Denis.IsLimit r := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := hrseq hrlim
    exact hasCoveringSequence_of_minimal s _ r hrlim hlen _
      (limit_rank_successor_index_succ_coveringFundamentalSequence s r b a _ hr hb haRep hmem haC
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality r hrlim)) f hf)

theorem hasCoveringSequence_zero_collapse (s : OCF.Denis.Supply) (k : Term) (hk : IsNormal s k)
    (hreg : OCF.Denis.RegularIndex s (denote s k))
    (hranks : ∀ r b, ZeroIndex.Subterm (.I r b) k → HasCoveringSequence s (denote s r)) :
    HasCoveringSequence s (OCF.Denis.psi s (denote s k) 0) := by
  obtain ⟨r, b, hs, hn, hr, hmem, heq⟩ := ZeroIndex.exists_normal_index s k hk hreg
  rw [heq]
  have hrseq := hranks r b hs
  cases hn with
  | index hrN hbN hrl hbl =>
    change HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) 0)
    rcases OCF.Denis.regular_I_argument s _ _ hbl (OCF.Denis.regularIndex_regular s _ hr) with hz | hsucc
    · rw [hz]
      exact hasCoveringSequence_first_index_zero s _ ⟨r, hrN, rfl⟩ hrseq
    · obtain ⟨c, hc⟩ := hsucc
      change OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) 0)
        (OCF.Denis.I s (denote s r) (denote s b)) at hmem
      rw [hc] at hmem ⊢
      exact hasCoveringSequence_successor_index_zero s _ c ⟨r, hrN, rfl⟩
        (represented_predecessor s c ⟨b, hbN, hc⟩) hrseq hmem

theorem hasCoveringSequence_collapse_of_index_not_mem (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a))
    (hnot : ¬ OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k))
    (ih : ∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasCoveringSequence s (denote s u)) :
    HasCoveringSequence s (denote s (.psi k a)) := by
  obtain ⟨l, b, hb, heq, hsize⟩ := CollapseNormalization.smaller_of_index_not_mem s k a hn hnot
  rw [← heq]
  exact ih (.psi l b) hsize hb

theorem hasCoveringSequence_nonlimit_collapse_induction (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (haNonlimit : denote s a = 0 ∨ ∃ c, denote s a = succ c)
    (ih : ∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasCoveringSequence s (denote s u)) :
    HasCoveringSequence s (denote s (.psi k a)) := by
  classical
  by_cases hmem : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)
  · cases hn with
    | collapse hk ha hreg harg =>
      obtain ⟨r, b, rfl⟩ := CollapseNormalization.normal_regular_is_index s k hk
        (OCF.Denis.regularIndex_regular s _ hreg)
      cases hk with
      | index hr hb hrl hbl =>
        have hrseq := ih r (by simp; omega) hr
        rcases haNonlimit with haz | hasucc
        · change HasCoveringSequence s (OCF.Denis.psi s (denote s (.I r b)) (denote s a))
          rw [haz]
          exact hasCoveringSequence_zero_collapse s (.I r b) (.index hr hb hrl hbl) hreg
            (fun q c hs => ih q (by have hh := hs.index_rank_size_lt; simp at hh ⊢; omega)
              ((ZeroIndex.Subterm.indexRank (.refl q)).trans hs |>.normal (.index hr hb hrl hbl)))
        · obtain ⟨c, hc⟩ := hasucc
          change HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
          change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
            (denote s a) at harg
          change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (OCF.Denis.I s (denote s r) (denote s b)) (denote s a))
            (OCF.Denis.I s (denote s r) (denote s b)) at hmem
          rw [hc] at harg hmem ⊢
          rcases OCF.Denis.regular_I_argument s _ _ hbl (OCF.Denis.regularIndex_regular s _ hreg) with hbz | hbs
          · rw [hbz] at harg ⊢
            exact hasCoveringSequence_first_index_succ s _ c ⟨r, hr, rfl⟩ ⟨a, ha, hc⟩ hrseq harg
          · obtain ⟨d, hd⟩ := hbs
            rw [hd] at harg hmem ⊢
            exact hasCoveringSequence_successor_index_succ s _ d c ⟨r, hr, rfl⟩
              (represented_predecessor s d ⟨b, hb, hd⟩) ⟨a, ha, hc⟩ hrseq hmem harg
  · exact hasCoveringSequence_collapse_of_index_not_mem s k a hn hmem ih

theorem hasCoveringSequence_I_small_parameters (s : OCF.Denis.Supply) (k r b : Term)
    (hn : IsNormal s (.psi k (.I r b))) (hb : OCF.Denis.IsLimit (denote s b))
    (hs : HasCoveringSequence s (denote s b))
    (hrk : denote s r < denote s k) (hbk : denote s b < denote s k)
    (hK : OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k)) :
    HasCoveringSequence s (denote s (.psi k (.I r b))) := by
  obtain ⟨hlen, f, hf⟩ := hs hb
  obtain ⟨_, _, _, hg⟩ := proper_I_small_parameters_coveringFundamentalSequence s k r b hn hK hrk hbk _
    (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality _ hb))
    (OCF.Denis.cofinality_addPrincipal _ hb) f hf
  exact hasCoveringSequence_of_minimal s _ _ hb hlen _ hg

theorem hasCoveringSequence_I_tree_parameter (s : OCF.Denis.Supply) (k r b : Term)
    (hn : IsNormal s (.psi k (.I r b))) (hb : OCF.Denis.IsLimit (denote s b))
    (hs : HasCoveringSequence s (denote s b))
    (hrTree : CollapseTree s r) (hbk : denote s b < denote s k)
    (hK : OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k)) :
    HasCoveringSequence s (denote s (.psi k (.I r b))) := by
  obtain ⟨hlen, f, hf⟩ := hs hb
  obtain ⟨_, _, _, hg⟩ := proper_I_tree_parameter_coveringFundamentalSequence s k r b hn hK hrTree hbk _
    (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality _ hb))
    (OCF.Denis.cofinality_addPrincipal _ hb) f hf
  exact hasCoveringSequence_of_minimal s _ _ hb hlen _ hg

theorem hasCoveringSequence_sum_tree_parameter (s : OCF.Denis.Supply) (k p b : Term)
    (hn : IsNormal s (.psi k (.add p b))) (hb : OCF.Denis.IsLimit (denote s b))
    (hs : HasCoveringSequence s (denote s b))
    (hpTree : CollapseTree s p) (hbk : denote s b < denote s k)
    (hK : OCF.Denis.C s (denote s (.add p b)) (denote s (.psi k (.add p b))) (denote s k)) :
    HasCoveringSequence s (denote s (.psi k (.add p b))) := by
  obtain ⟨hlen, f, hf⟩ := hs hb
  obtain ⟨_, _, _, hg⟩ := proper_sum_tree_parameter_coveringFundamentalSequence s k p b hn hK hpTree hbk _
    (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality _ hb))
    (OCF.Denis.cofinality_addPrincipal _ hb) f hf
  exact hasCoveringSequence_of_minimal s _ _ hb hlen _ hg

/-- The sole remaining clause for the stronger structural induction:
a proper collapse at a non-regular limit argument at least its index.
This is an explicit, still unproved proposition, not an axiom. -/
def LargeLimitCoveringStep (s : OCF.Denis.Supply) : Prop :=
  ∀ k a, IsNormal s (.psi k a) → OCF.Denis.IsLimit (denote s a) →
    ¬ OCF.Denis.UncountableRegular (denote s a) → denote s k ≤ denote s a →
    OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) →
    (∀ u, sizeOf u < sizeOf (Term.psi k a) → IsNormal s u → HasCoveringSequence s (denote s u)) →
    HasCoveringSequence s (denote s (.psi k a))

theorem normal_hasCoveringSequence_of_large_limit (s : OCF.Denis.Supply) (hlarge : LargeLimitCoveringStep s)
    (t : Term) (ht : IsNormal s t) : HasCoveringSequence s (denote s t) := by
  classical
  induction t using (measure (fun t : Term => sizeOf t)).wf.induction with
  | h t ih =>
    cases ht with
    | zero => exact hasCoveringSequence_zero s
    | @sum p a hp ha hpp hpv hapos hhead =>
      exact hasCoveringSequence_add s _ _ ⟨p, hp, rfl⟩ ((zero_lt_iff_ne_zero _).mp hapos)
        (ih a (by change sizeOf a < sizeOf (Term.add p a); simp; omega) ha)
    | @index r a hr ha hrl hal =>
      exact hasCoveringSequence_I s _ _ ⟨r, hr, rfl⟩ ⟨a, ha, rfl⟩
        (ih a (by change sizeOf a < sizeOf (Term.I r a); simp; omega) ha)
    | @collapse k a hk ha hreg harg =>
      have hn : IsNormal s (.psi k a) := .collapse hk ha hreg harg
      by_cases hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k)
      · by_cases halim : OCF.Denis.IsLimit (denote s a)
        · by_cases hbound : denote s a < denote s k
          · exact hasCoveringSequence_proper_limit_below s k a hn halim
              (ih a (by change sizeOf a < sizeOf (Term.psi k a); simp; omega) ha) hbound hK
          · by_cases hareg : OCF.Denis.UncountableRegular (denote s a)
            · exact hasCoveringSequence_proper_regular_argument s k a hn hareg hK
            · exact hlarge k a hn halim hareg ((not_lt_iff_le _ _).mp hbound) hK ih
        · apply hasCoveringSequence_nonlimit_collapse_induction s k a hn _ ih
          by_cases hz : denote s a = 0
          · exact Or.inl hz
          by_cases hs : ∃ c, denote s a = succ c
          · exact Or.inr hs
          · exact False.elim (halim ⟨hz, hs⟩)
      · exact hasCoveringSequence_collapse_of_index_not_mem s k a hn hK ih

theorem largeLimitCoveringStep_iff_all_normal (s : OCF.Denis.Supply) :
    LargeLimitCoveringStep s ↔ ∀ t, IsNormal s t → HasCoveringSequence s (denote s t) :=
  ⟨fun h => normal_hasCoveringSequence_of_large_limit s h,
    fun h k a hn _ _ _ _ _ => h (.psi k a) hn⟩

theorem normal_hasNormalSequence_of_large_limit (s : OCF.Denis.Supply) (hlarge : LargeLimitCoveringStep s)
    (t : Term) (ht : IsNormal s t) : HasNormalSequence s (denote s t) :=
  (normal_hasCoveringSequence_of_large_limit s hlarge t ht).to_normal

/-- A proved family for the stronger invariant. In particular the
limit constructor permits arbitrary nesting at uncountable lengths.
This is not a replacement definition for all normal terms. -/
inductive CoveringSequenceTerm (s : OCF.Denis.Supply) : Term → Prop where
  | zero : CoveringSequenceTerm s .zero
  | countable {t : Term} : SequenceTerm s t →
      (∀ ha, OCF.Denis.cofinality (denote s t) ha = OCF.Denis.omega) → CoveringSequenceTerm s t
  | regular {t : Term} : IsNormal s t → OCF.Denis.UncountableRegular (denote s t) → CoveringSequenceTerm s t
  | sum {p a : Term} : CoveringSequenceTerm s a → IsNormal s (.add p a) → CoveringSequenceTerm s (.add p a)
  | index {r a : Term} : CoveringSequenceTerm s a → IsNormal s (.I r a) → CoveringSequenceTerm s (.I r a)
  | properLimit {k a : Term} : CoveringSequenceTerm s a → IsNormal s (.psi k a) →
      OCF.Denis.IsLimit (denote s a) → denote s a < denote s k →
      OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) → CoveringSequenceTerm s (.psi k a)
  | regularArgument {k a : Term} : IsNormal s (.psi k a) → OCF.Denis.UncountableRegular (denote s a) →
      OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) → CoveringSequenceTerm s (.psi k a)
  | smallIndexArgument {k r b : Term} : CoveringSequenceTerm s b → IsNormal s (.psi k (.I r b)) →
      OCF.Denis.IsLimit (denote s b) → denote s r < denote s k → denote s b < denote s k →
      OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k) →
      CoveringSequenceTerm s (.psi k (.I r b))
  | treeIndexArgument {k r b : Term} : CoveringSequenceTerm s b → IsNormal s (.psi k (.I r b)) →
      OCF.Denis.IsLimit (denote s b) → CollapseTree s r → denote s b < denote s k →
      OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k) →
      CoveringSequenceTerm s (.psi k (.I r b))
  | treeSumArgument {k p b : Term} : CoveringSequenceTerm s b → IsNormal s (.psi k (.add p b)) →
      OCF.Denis.IsLimit (denote s b) → CollapseTree s p → denote s b < denote s k →
      OCF.Denis.C s (denote s (.add p b)) (denote s (.psi k (.add p b))) (denote s k) →
      CoveringSequenceTerm s (.psi k (.add p b))
  | equalValue {t u : Term} : CoveringSequenceTerm s u → IsNormal s t → denote s t = denote s u →
      CoveringSequenceTerm s t

theorem CoveringSequenceTerm.hasCoveringSequence {s : OCF.Denis.Supply} {t : Term}
    (ht : CoveringSequenceTerm s t) : HasCoveringSequence s (denote s t) := by
  induction ht with
  | zero => exact hasCoveringSequence_zero s
  | countable ht hcof => exact hasCoveringSequence_of_countable s _ ht.hasNormalSequence hcof
  | regular hn hr => exact hasCoveringSequence_regular s _ hr ⟨_, hn, rfl⟩
  | @sum p a ha hn ih =>
    cases hn with
    | sum hp ha hpp hpv hapos hhead =>
      exact hasCoveringSequence_add s _ _ ⟨p, hp, rfl⟩ ((zero_lt_iff_ne_zero _).mp hapos) ih
  | @index r a ha hn ih =>
    cases hn with
    | index hr ha hrl hal => exact hasCoveringSequence_I s _ _ ⟨r, hr, rfl⟩ ⟨a, ha, rfl⟩ ih
  | @properLimit k a ha hn halim hbound hK ih =>
    exact hasCoveringSequence_proper_limit_below s k a hn halim ih hbound hK
  | @regularArgument k a hn hr hK => exact hasCoveringSequence_proper_regular_argument s k a hn hr hK
  | @smallIndexArgument k r b hb hn hlim hrk hbk hK ih =>
    exact hasCoveringSequence_I_small_parameters s k r b hn hlim ih hrk hbk hK
  | @treeIndexArgument k r b hb hn hlim hrTree hbk hK ih =>
    exact hasCoveringSequence_I_tree_parameter s k r b hn hlim ih hrTree hbk hK
  | @treeSumArgument k p b hb hn hlim hpTree hbk hK ih =>
    exact hasCoveringSequence_sum_tree_parameter s k p b hn hlim ih hpTree hbk hK
  | equalValue hu hn heq ih => rwa [heq]

theorem hasCoveringSequence_first_index_collapse (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : Represented s a) (hrseq : HasCoveringSequence s r)
    (haseq : HasCoveringSequence s a)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r 0) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s r 0) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r 0) a) := by
  classical
  by_cases hz : a = 0
  · subst a
    exact hasCoveringSequence_first_index_zero s r hr hrseq
  by_cases hs : ∃ c, a = succ c
  · obtain ⟨c, rfl⟩ := hs
    exact hasCoveringSequence_first_index_succ s r c hr ha hrseq harg
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hs⟩
    have hrank : OCF.Denis.RankBounded s r := by
      obtain ⟨rt, hrt, rfl⟩ := hr
      exact normal_rankBounded s rt hrt
    obtain ⟨hlen, f, hf⟩ := haseq halim
    apply hasCoveringSequence_of_minimal s _ a halim hlen _
    apply psi_coveringFundamentalSequence s _ a _ (represented_I s r 0 hr ⟨.zero, .zero, rfl⟩)
      (Or.inl ⟨r, rfl⟩)
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf
    · exact fun _ _ => OCF.Denis.first_rank_index_mem s r _ hrank
    · intro i hi
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f i)
        (hbound halim) harg (hf.normalSequence.fundamental.below i hi))

theorem hasCoveringSequence_successor_index_collapse (s : OCF.Denis.Supply) (r b a : OCF.Denis.O)
    (hr : Represented s r) (hb : Represented s b) (ha : Represented s a)
    (hrseq : HasCoveringSequence s r) (haseq : HasCoveringSequence s a)
    (hmem : OCF.Denis.C s 0 (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) 0) (OCF.Denis.I s r (succ b)))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a)
    (hbound : OCF.Denis.IsLimit a → a < OCF.Denis.I s r (succ b)) :
    HasCoveringSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) := by
  classical
  have hindex (c : OCF.Denis.O) :
      OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) c) (OCF.Denis.I s r (succ b)) :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ 0 c (zero_le c)) _
      (OCF.Denis.C_mono_argument s 0 c _ (zero_le c) _ hmem)
  by_cases hz : a = 0
  · subst a
    exact hasCoveringSequence_successor_index_zero s r b hr hb hrseq hmem
  by_cases hs : ∃ c, a = succ c
  · obtain ⟨c, rfl⟩ := hs
    exact hasCoveringSequence_successor_index_succ s r b c hr hb ha hrseq (hindex _) harg
  · have halim : OCF.Denis.IsLimit a := ⟨hz, hs⟩
    obtain ⟨hlen, f, hf⟩ := haseq halim
    apply hasCoveringSequence_of_minimal s _ a halim hlen _
    apply psi_coveringFundamentalSequence s _ a _
      (represented_I s r (succ b) hr (represented_succ s b hb)) (Or.inr ⟨r, b, rfl⟩)
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0) (OCF.Denis.omega_le_cofinality a halim)) f hf
    · exact fun i _ => hindex (f i)
    · intro i hi
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ a (f i)
        (hbound halim) harg (hf.normalSequence.fundamental.below i hi))

theorem SequenceTerm.hasCoveringSequence {s : OCF.Denis.Supply} {t : Term} (ht : SequenceTerm s t) :
    HasCoveringSequence s (denote s t) := by
  induction ht with
  | @bounded t ht hbound =>
    intro hlim
    exact hasCoveringSequence_of_dense s _ (normal_dense_below_first_diagonal s t ht hbound hlim) hlim
  | successor _ hs =>
    obtain ⟨a, heq⟩ := hs
    rw [heq]
    exact hasCoveringSequence_succ s a
  | @regular t ht hreg => exact hasCoveringSequence_regular s _ hreg ⟨t, ht, rfl⟩
  | @sum a b hb hn ih =>
    cases hn with
    | sum ha hb hap hp hbpos hhead =>
      exact hasCoveringSequence_add s _ _ ⟨a, ha, rfl⟩ ((zero_lt_iff_ne_zero _).mp hbpos) ih
  | @index r b hb hn ih =>
    cases hn with
    | index hr hb hrl hbl => exact hasCoveringSequence_I s _ _ ⟨r, hr, rfl⟩ ⟨b, hb, rfl⟩ ih
  | @first k a ha hn heq hbound ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg ⊢
      exact hasCoveringSequence_first_index_collapse s 0 _ ⟨.zero, .zero, rfl⟩ ⟨a, ha, rfl⟩
        (hasCoveringSequence_zero s) ih harg hbound
  | @successorRank k a r hr ha hn heq hbound ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hbound ⊢
      exact hasCoveringSequence_first_index_collapse s _ _ (represented_succ s _ ⟨r, hr, rfl⟩)
        ⟨a, ha, rfl⟩ (hasCoveringSequence_succ s _) ih harg hbound
  | @firstIndex k a r hr ha hn heq hbound ihr iha =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hbound ⊢
      exact hasCoveringSequence_first_index_collapse s _ _ ⟨r, hr.normal, rfl⟩ ⟨a, ha, rfl⟩ ihr iha harg hbound
  | @successorIndexZero k a r b hr hb hn heq haz hmem ihr =>
    change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
    rw [heq] at hmem
    rw [heq, haz]
    exact hasCoveringSequence_successor_index_zero s _ _ ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩ ihr hmem
  | @successorIndexSucc k a r b hr hb hn heq has hmem ihr =>
    cases hn with
    | collapse hk ha hreg harg =>
      obtain ⟨c, hc⟩ := has
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq, hc] at harg hmem ⊢
      exact hasCoveringSequence_successor_index_succ s _ _ c ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩
        ⟨a, ha, hc⟩ ihr hmem harg
  | @successorIndex k a r b hr ha hb hn heq hmem hbound ihr iha =>
    cases hn with
    | collapse hk haN hreg harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [heq] at harg hmem hbound ⊢
      exact hasCoveringSequence_successor_index_collapse s _ _ _ ⟨r, hr.normal, rfl⟩ ⟨b, hb, rfl⟩
        ⟨a, haN, rfl⟩ ihr iha hmem harg hbound
  | @countableLimit k a ha hn halim hcof hbound hindex ih =>
    exact hasCoveringSequence_proper_limit_below s k a hn halim ih hbound hindex
  | @successorIndexLimitTail k a r b ha hr hb hn heq halim hbl hbound ih =>
    have hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k) := by
      cases hn with
      | collapse hk haN hreg harg =>
        have hbarg := OCF.Ordinal.lt_of_lt_of_le hbl (OCF.Denis.cofinality_le_self _ halim)
        have hbvalue := OCF.Ordinal.lt_trans _ _ _ hbarg (OCF.Denis.psi_closed s _ _ _ harg hbound)
        change OCF.Denis.C s (denote s a) (OCF.Denis.psi s (denote s k) (denote s a)) (denote s k)
        rw [heq] at hbvalue ⊢
        exact (OCF.Denis.C_successor_index_iff_parameter s _ _ _ (normal_rankBounded s r hr)).mpr hbvalue
    exact hasCoveringSequence_proper_limit_below s k a hn halim ih hbound hK
  | @zeroCollapse k a hranks hn haz ih =>
    cases hn with
    | collapse hk ha hreg harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s a))
      rw [haz]
      exact hasCoveringSequence_zero_collapse s k hk hreg ih
  | @regularArgument k a hn hr hK => exact hasCoveringSequence_proper_regular_argument s k a hn hr hK
  | @countableSumArgument k p b hb hn hlim hcof hbound hK ih =>
    obtain ⟨_, f, hf⟩ := ih hlim
    rw [hcof] at hf
    cases hn with
    | collapse hk ha hreg harg =>
      have hpC := C_normal_sum_head s _ _ p b ha harg
      have hbC := OCF.Denis.C_suffix s _ _ _ (denote s p) (denote s b) harg rfl
      cases ha with
      | sum hp hbN hpp hpv hbpos hhead =>
        exact hasCoveringSequence_of_dense s _ (proper_sum_countable_dense s _ _ _ hreg
          ⟨k, hk, rfl⟩ ⟨p, hp, rfl⟩ hlim hf.normalSequence.omega_dense
          (OCF.Denis.psi_closed s _ _ _ hbC hbound) hpC hK)
  | @countableIndexArgument k r b hb hn hlim hcof hbound hK ih =>
    obtain ⟨_, f, hf⟩ := ih hlim
    rw [hcof] at hf
    cases hn with
    | collapse hk ha hreg harg =>
      cases ha with
      | index hr hbN hrl hbl =>
        exact hasCoveringSequence_of_dense s _ (proper_normal_I_countable_dense s _ _ _ hreg
          ⟨k, hk, rfl⟩ ⟨r, hr, rfl⟩ hlim hf.normalSequence.omega_dense hrl hbl hbound hK harg)
  | @diagonal k t ht hn heq hreg =>
    cases hn with
    | collapse hk htN _ harg =>
      change HasCoveringSequence s (OCF.Denis.psi s (denote s k) (denote s t))
      rw [heq] at harg ⊢
      exact hasCoveringSequence_of_dense s _ (collapseTree_diagonal_dense s t ht hreg harg)
  | equalValue _ _ heq ih => rwa [heq]

end
end T.Correspondence.Denis.Covering
