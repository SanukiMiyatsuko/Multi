import Multi.term3.Denis.NormalAddition

/-! Normal forms at normal indices, with ordinal (not just natural-number)
domains. For omega every index is represented. For regular uncountable
domains the identity rule preserves every represented index, while its
semantic extension is defined on all ordinal indices. No general psi
normality or density premise is hidden by this interface. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

structure NormalFundamentalSequence (s : OCF.Denis.Supply) (a length : OCF.Denis.O)
    (f : OCF.Denis.O → OCF.Denis.O) : Prop where
  fundamental : OCF.Denis.TransfiniteFundamentalSequence a length f
  normal : ∀ i, i < length → Represented s i → Represented s (f i)

theorem NormalFundamentalSequence.minimal {s : OCF.Denis.Supply} {a b : OCF.Denis.O}
    (hb : OCF.Denis.IsLimit b) {f : OCF.Denis.O → OCF.Denis.O}
    (hf : NormalFundamentalSequence s a (OCF.Denis.cofinality b hb) f) :
    OCF.Denis.cofinality a (hf.fundamental.isLimit
      (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.finite_lt_omega 0)
        (OCF.Denis.omega_le_cofinality b hb))) = OCF.Denis.cofinality b hb :=
  OCF.Denis.cofinality_eq_of_minimal_length hb hf.fundamental

theorem revised_cofinality (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a) :
    OCF.Denis.cofinality a ha = OCF.Denis.omega :=
  OCF.Denis.cofinality_eq_omega_of_fundamentalSequence
    (revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd)

theorem not_dense_of_uncountable_cofinality (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hc : OCF.Denis.omega < OCF.Denis.cofinality a ha) :
    ¬ DenseBelow s a := by
  intro hd
  rw [revised_cofinality s a ha hd] at hc
  exact OCF.Ordinal.lt_irrefl _ hc

theorem revised_normalFundamentalSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a) :
    NormalFundamentalSequence s a OCF.Denis.omega
      (fun i => revisedValue s a (OCF.Denis.finiteIndex i)) :=
  ⟨(revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd).transfinite,
    fun i _ _ => revisedValue_represented s a (OCF.Denis.finiteIndex i)⟩

theorem regular_normalFundamentalSequence (s : OCF.Denis.Supply) (k : OCF.Denis.O)
    (hk : OCF.Denis.UncountableRegular k) : NormalFundamentalSequence s k k (fun i => i) :=
  ⟨OCF.Denis.regular_fundamentalSequence k hk, fun _ _ hi => hi⟩

theorem add_normalFundamentalSequence (s : OCF.Denis.Supply) (b a length : OCF.Denis.O)
    (hb : Represented s b) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : NormalFundamentalSequence s a length f) :
    NormalFundamentalSequence s (b + a) length (fun i => b + f i) :=
  ⟨OCF.Denis.add_transfiniteFundamentalSequence b a length f hl hf.fundamental,
    fun i hi hn => represented_add s b (f i) hb (hf.normal i hi hn)⟩

theorem I_normalFundamentalSequence (s : OCF.Denis.Supply) (r a length : OCF.Denis.O)
    (hr : Represented s r) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : NormalFundamentalSequence s a length f) :
    NormalFundamentalSequence s (OCF.Denis.I s r a) length (fun i => OCF.Denis.I s r (f i)) :=
  ⟨OCF.Denis.I_transfiniteFundamentalSequence s r a length f hl hf.fundamental,
    fun i hi hn => represented_I s r (f i) hr (hf.normal i hi hn)⟩

theorem represented_psi_of_mem (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : Represented s k) (ha : Represented s a) (hreg : OCF.Denis.RegularIndex s k)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s k a) a) :
    Represented s (OCF.Denis.psi s k a) := by
  obtain ⟨kt, hkt, rfl⟩ := hk
  obtain ⟨argt, hargt, rfl⟩ := ha
  exact ⟨.psi kt argt, .collapse hkt hargt hreg harg, rfl⟩

theorem psi_normalFundamentalSequence (s : OCF.Denis.Supply) (k a length : OCF.Denis.O)
    (hk : Represented s k) (hreg : OCF.Denis.RegularIndex s k) (hl : 0 < length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s a length f)
    (hindex : ∀ i, i < length → OCF.Denis.C s (f i) (OCF.Denis.psi s k (f i)) k)
    (harg : ∀ i, i < length → OCF.Denis.C s (f i) (OCF.Denis.psi s k (f i)) (f i)) :
    NormalFundamentalSequence s (OCF.Denis.psi s k a) length (fun i => OCF.Denis.psi s k (f i)) :=
  ⟨OCF.Denis.psi_transfiniteFundamentalSequence s k a length f hreg hl hf.fundamental hindex harg,
    fun i hi hn => represented_psi_of_mem s k (f i) hk (hf.normal i hi hn) hreg (harg i hi)⟩

theorem NormalFundamentalSequence.omega_dense {s : OCF.Denis.Supply} {a : OCF.Denis.O}
    {f : OCF.Denis.O → OCF.Denis.O} (hf : NormalFundamentalSequence s a OCF.Denis.omega f) :
    DenseBelow s a := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hf.fundamental.cofinal x hx
  obtain ⟨n, rfl⟩ := (OCF.Denis.lt_omega_iff i).mp hi
  exact ⟨f (OCF.Denis.finite n), hf.normal _ hi (finite_represented s n), hxi,
    hf.fundamental.below _ hi⟩

theorem dense_iff_exists_normalFundamentalSequence (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) :
    DenseBelow s a ↔ ∃ f, NormalFundamentalSequence s a OCF.Denis.omega f :=
  ⟨fun hd => ⟨_, revised_normalFundamentalSequence s a ha hd⟩,
    fun ⟨_, hf⟩ => hf.omega_dense⟩

/-- The repaired expansion works for the entire successor-rank zero family,
not only for the first inaccessible-cardinal example. -/
theorem successor_rank_zero_dense (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) : DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0) := by
  obtain ⟨rt, hrt, rfl⟩ := hr
  apply dense_of_normal_sequence s _ _ (successor_rank_zero_fundamentalSequence s rt hrt)
  intro n
  exact ⟨indexIterTerm rt n, indexIterTerm_isNormal s rt hrt n, denote_indexIterTerm s rt n⟩

theorem revised_successor_rank_zero_fundamentalSequence (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0)
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0)) := by
  apply revised_fundamentalSequence_of_dense s _ _ (successor_rank_zero_dense s r hr)
  exact OCF.Denis.psi_pos s _ _
    (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ (Or.inl ⟨succ r, rfl⟩)))

theorem revised_successor_rank_zero_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r : OCF.Denis.O) (hr : Represented s r) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0) OCF.Denis.omega
      (fun i => revisedValue s (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0)
        (OCF.Denis.finiteIndex i)) :=
  ⟨(revised_successor_rank_zero_fundamentalSequence s r hr).transfinite,
    fun _ _ _ => revisedValue_represented s _ _⟩

theorem successor_rank_zero_cofinality (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : Represented s r) :
    OCF.Denis.cofinality (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) 0)
      (revised_successor_rank_zero_fundamentalSequence s r hr).isLimit = OCF.Denis.omega :=
  OCF.Denis.cofinality_eq_omega_of_fundamentalSequence
    (revised_successor_rank_zero_fundamentalSequence s r hr)

end
end T.Correspondence.Denis.Covering
