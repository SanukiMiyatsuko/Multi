import Multi.term3.Denis.LimitRankSequences

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
  | diagonal {k t : Term} : CollapseTree s t → IsNormal s (.psi k t) →
      denote s k = OCF.Denis.I s 0 0 → OCF.Denis.RegularIndex s (denote s t) → SequenceTerm s (.psi k t)
  | equalValue {t u : Term} : SequenceTerm s u → IsNormal s t → denote s t = denote s u → SequenceTerm s t

theorem SequenceTerm.normal {s : OCF.Denis.Supply} {t : Term} (ht : SequenceTerm s t) : IsNormal s t := by
  cases ht <;> assumption

/-- Pull a proved sequence branch back across the terminating nested-index
normalization. This turns every normal term whose normalized presentation is
already in `SequenceTerm` into a member of the assembled family without
changing its ordinal value. -/
theorem SequenceTerm.of_nested_normalize {s : OCF.Denis.Supply} {t : Term}
    (ht : IsNormal s t) (hn : SequenceTerm s (Nested.normalize s t)) : SequenceTerm s t :=
  .equalValue hn ht (Nested.denote_normalize s t).symm

/-- A direct integration rule for the proved nested successor-parameter
rewrite. In particular this covers collapse indices of the form
`I(q, succ (psi (I(r,b),t)))` whenever the replacement branch is already
assembled. -/
theorem SequenceTerm.of_nested_collapse {s : OCF.Denis.Supply} {q r b t a : Term}
    (hn : IsNormal s (nestedCollapse q r b t a))
    (hqr : denote s q < denote s r) (hat : denote s a ≤ denote s t)
    (hseq : SequenceTerm s (.psi (.I r b) a)) :
    SequenceTerm s (nestedCollapse q r b t a) := by
  have h := nestedCollapse_replacement_normal s q r b t a hn hqr hat
  exact .equalValue hseq hn h.2

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

end
end T.Correspondence.Denis.Covering
