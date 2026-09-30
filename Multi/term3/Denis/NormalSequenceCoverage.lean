import Multi.term3.Denis.IndexStageInterpolation

/-! Fundamental sequences with cofinality also at represented indices.
This extra property supplies represented tail offsets. It is proved
for the constructors below, not inferred merely from normal outputs. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem normal_suffix_represented (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (p y : OCF.Denis.O) (heq : denote s t = p + y) : Represented s y := by
  classical
  induction ht generalizing p y with
  | zero =>
    have hy := right_le_add p y
    change 0 = p + y at heq
    rw [← heq] at hy
    rw [le_antisymm hy (zero_le y)]
    exact ⟨.zero, .zero, rfl⟩
  | @index r b hr hb hrl hbl ihr ihb =>
    rcases OCF.Denis.addPrincipal_suffix (OCF.Denis.I_addPrincipal s _ _) heq with hy | hy
    · rw [hy]; exact ⟨.zero, .zero, rfl⟩
    · exact ⟨.I r b, .index hr hb hrl hbl, hy.symm⟩
  | @collapse k a hk ha hreg harg ihk iha =>
    rcases OCF.Denis.addPrincipal_suffix
      (OCF.Denis.psi_addPrincipal s _ _ (OCF.Denis.regularIndex_regular s _ hreg)) heq with hy | hy
    · rw [hy]; exact ⟨.zero, .zero, rfl⟩
    · exact ⟨.psi k a, .collapse hk ha hreg harg, hy.symm⟩
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    by_cases hpu : p < denote s u
    · have habs : p + denote s (.add u v) = denote s (.add u v) := hp.absorb_of_le hpu (le_add _ _)
      have hy := add_right_cancel (heq.symm.trans habs.symm)
      exact ⟨.add u v, .sum hu hv hup hp hvpos hhead, hy.symm⟩
    · obtain ⟨c, hc⟩ := exists_add_of_le (denote s u) p ((not_lt_iff_le _ _).mp hpu)
      change denote s u + denote s v = p + y at heq
      rw [hc, add_assoc] at heq
      exact ihv c y (add_right_cancel heq)

theorem represented_limit_add_interpolation (s : OCF.Denis.Supply) (p a x : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (hx : Represented s x) (hlt : x < p + a) :
    ∃ c, Represented s c ∧ c < a ∧ x < p + c := by
  classical
  by_cases hxp : x < p
  · exact ⟨0, ⟨.zero, .zero, rfl⟩, (zero_lt_iff_ne_zero a).mpr ha.1, by simpa only [add_zero] using hxp⟩
  obtain ⟨y, hy⟩ := exists_add_of_le p x ((not_lt_iff_le _ _).mp hxp)
  have hyRep : Represented s y := by
    obtain ⟨t, ht, rfl⟩ := hx
    exact normal_suffix_represented s t ht p y hy
  have hya : y < a := by
    apply Classical.byContradiction
    intro hn
    have h := add_mono_right p ((not_lt_iff_le _ _).mp hn)
    rw [hy] at hlt
    exact OCF.Ordinal.lt_irrefl _ (OCF.Ordinal.lt_of_lt_of_le hlt h)
  refine ⟨succ y, represented_succ s y hyRep, OCF.Denis.succ_lt_limit ha hya, ?_⟩
  rw [hy]
  exact add_lt_add_right p (lt_succ_self y)

structure CoveringFundamentalSequence (s : OCF.Denis.Supply) (a length : OCF.Denis.O)
    (f : OCF.Denis.O → OCF.Denis.O) : Prop where
  normalSequence : NormalFundamentalSequence s a length f
  cofinal_normal : ∀ x, Represented s x → x < a →
    ∃ i, Represented s i ∧ i < length ∧ x < f i

theorem coveringFundamentalSequence_of_omega (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s a OCF.Denis.omega f) :
    CoveringFundamentalSequence s a OCF.Denis.omega f := by
  refine ⟨hf, fun x _ hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ := hf.fundamental.cofinal x hx
  obtain ⟨n, rfl⟩ := (OCF.Denis.lt_omega_iff i).mp hi
  exact ⟨_, finite_represented s n, hi, hxi⟩

theorem regular_coveringFundamentalSequence (s : OCF.Denis.Supply) (k : OCF.Denis.O)
    (hk : OCF.Denis.UncountableRegular k) : CoveringFundamentalSequence s k k (fun i => i) :=
  ⟨regular_normalFundamentalSequence s k hk, fun x hx hxl =>
    ⟨succ x, represented_succ s x hx, OCF.Denis.regular_succ_lt hk hxl, lt_succ_self x⟩⟩

theorem CoveringFundamentalSequence.shift {s : OCF.Denis.Supply} {a length : OCF.Denis.O}
    {f : OCF.Denis.O → OCF.Denis.O} (hf : CoveringFundamentalSequence s a length f)
    (c : OCF.Denis.O) (hadd : AddPrincipal length) (hc : c < length) (hcRep : Represented s c) :
    CoveringFundamentalSequence s a length (fun i => f (c + i)) := by
  refine ⟨hf.normalSequence.shift c hadd hc hcRep, fun x hx hxa => ?_⟩
  obtain ⟨i, hiRep, hi, hxi⟩ := hf.cofinal_normal x hx hxa
  exact ⟨i, hiRep, hi, OCF.Ordinal.lt_of_lt_of_le hxi
    (hf.normalSequence.fundamental.mono (right_le_add c i) (hadd c i hc hi))⟩

theorem add_coveringFundamentalSequence (s : OCF.Denis.Supply) (p a length : OCF.Denis.O)
    (hp : Represented s p) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s a length f) :
    CoveringFundamentalSequence s (p + a) length (fun i => p + f i) := by
  refine ⟨add_normalFundamentalSequence s p a length hp hl f hf.normalSequence, fun x hx hxa => ?_⟩
  obtain ⟨c, hc, hca, hxc⟩ := represented_limit_add_interpolation s p a x
    (hf.normalSequence.fundamental.isLimit hl) hx hxa
  obtain ⟨i, hiRep, hi, hci⟩ := hf.cofinal_normal c hc hca
  exact ⟨i, hiRep, hi, OCF.Ordinal.lt_trans _ _ _ hxc (add_lt_add_right p hci)⟩

theorem I_coveringFundamentalSequence (s : OCF.Denis.Supply) (r a length : OCF.Denis.O)
    (hr : Represented s r) (hl : 0 < length) (f : OCF.Denis.O → OCF.Denis.O)
    (hf : CoveringFundamentalSequence s a length f) :
    CoveringFundamentalSequence s (OCF.Denis.I s r a) length (fun i => OCF.Denis.I s r (f i)) := by
  refine ⟨I_normalFundamentalSequence s r a length hr hl f hf.normalSequence, fun x hx hxa => ?_⟩
  obtain ⟨c, hc, hca, hxc⟩ := represented_limit_index_interpolation s r a x hr
    (hf.normalSequence.fundamental.isLimit hl) hx hxa
  obtain ⟨i, hiRep, hi, hci⟩ := hf.cofinal_normal c hc hca
  exact ⟨i, hiRep, hi, OCF.Ordinal.lt_trans _ _ _ hxc (OCF.Denis.I_strict s r hci)⟩

theorem psi_coveringFundamentalSequence (s : OCF.Denis.Supply) (k a length : OCF.Denis.O)
    (hk : Represented s k) (hreg : OCF.Denis.RegularIndex s k) (hl : 0 < length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s a length f)
    (hindex : ∀ i, i < length → OCF.Denis.C s (f i) (OCF.Denis.psi s k (f i)) k)
    (harg : ∀ i, i < length → OCF.Denis.C s (f i) (OCF.Denis.psi s k (f i)) (f i)) :
    CoveringFundamentalSequence s (OCF.Denis.psi s k a) length (fun i => OCF.Denis.psi s k (f i)) := by
  refine ⟨psi_normalFundamentalSequence s k a length hk hreg hl f hf.normalSequence hindex harg,
    fun x hx hxa => ?_⟩
  obtain ⟨c, hc, hca, hxc⟩ := represented_limit_collapse_interpolation s k a x hreg
    (hf.normalSequence.fundamental.isLimit hl) hx hxa
  obtain ⟨i, hiRep, hi, hci⟩ := hf.cofinal_normal c hc hca
  exact ⟨i, hiRep, hi, OCF.Ordinal.lt_of_lt_of_le hxc (OCF.Denis.psi_mono s k c (f i) (Or.inl hci))⟩

theorem proper_limit_below_coveringFundamentalSequence (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a)) (hbound : denote s a < denote s k)
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k))
    (length : OCF.Denis.O) (hl : 0 < length) (hadd : AddPrincipal length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s (denote s a) length f) :
    ∃ c, Represented s c ∧ c < length ∧
      CoveringFundamentalSequence s (denote s (.psi k a)) length
        (fun i => OCF.Denis.psi s (denote s k) (f (c + i))) := by
  obtain ⟨d, hd, hda, hstage⟩ := proper_index_mem_at_represented_stage s k a hn
    (hf.normalSequence.fundamental.isLimit hl) hK
  obtain ⟨c, hc, hcl, hdc⟩ := hf.cofinal_normal d hd hda
  have hindex : OCF.Denis.C s (f c) (OCF.Denis.psi s (denote s k) (f c)) (denote s k) :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ d (f c) (Or.inl hdc)) _
      (OCF.Denis.C_mono_argument s _ _ _ (Or.inl hdc) _ hstage)
  have hshift := hf.shift c hadd hcl hc
  cases hn with
  | collapse hk ha hreg harg =>
    refine ⟨c, hc, hcl, psi_coveringFundamentalSequence s _ _ length ⟨k, hk, rfl⟩ hreg hl _ hshift ?_ ?_⟩
    · exact OCF.Denis.psi_tail_index_mem s _ _ length c f hf.normalSequence.fundamental hadd hcl hindex
    · intro i hi
      exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s _ _ _ hbound harg
        (hshift.normalSequence.fundamental.below i hi))

end
end T.Correspondence.Denis.Covering
