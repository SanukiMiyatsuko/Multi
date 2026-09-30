import Multi.term3.Denis.NormalLimitTransfer

/-! Tails of ordinal-indexed normal fundamental sequences. A represented
offset preserves representability of the indices. In particular, a
successor-index parameter below the domain gives an explicit admissible
offset; no choice of an unrepresented ordinal is used for that offset. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem TransfiniteFundamentalSequence.index_le_value {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (i : O) (hi : i < length) : i ≤ f i := by
  induction i using lt_wellFounded.induction with
  | h i ih =>
    apply (not_lt_iff_le _ _).mp
    intro hfi
    exact lt_irrefl _ (lt_of_le_of_lt (ih _ hfi (lt_trans _ _ _ hfi hi)) (hf.strict _ _ hfi hi))

theorem TransfiniteFundamentalSequence.shift {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (c : O)
    (hl : AddPrincipal length) (hc : c < length) :
    TransfiniteFundamentalSequence a length (fun i => f (c + i)) := by
  refine ⟨fun i hi => hf.below _ (hl c i hc hi),
    fun i j hij hj => hf.strict _ _ (add_lt_add_right c hij) (hl c j hc hj), ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hf.cofinal x hx
  exact ⟨i, hi, lt_of_lt_of_le hxi (hf.mono (right_le_add c i) (hl c i hc hi))⟩

theorem cofinality_addPrincipal (a : O) (ha : IsLimit a) : AddPrincipal (cofinality a ha) := by
  rcases omega_le_cofinality a ha with h | h
  · exact fun _ _ hx hy => regular_add_closed (cofinality_uncountableRegular a ha h) hx hy
  · rw [← h]
    exact fun _ _ hx hy => omega_add_closed hx hy

theorem psi_tail_index_mem (s : Supply) (k a length c : O) (f : O → O)
    (hf : TransfiniteFundamentalSequence a length f) (hadd : AddPrincipal length) (hc : c < length)
    (hk : C s (f c) (psi s k (f c)) k) :
    ∀ i, i < length → C s (f (c + i)) (psi s k (f (c + i))) k := by
  intro i hi
  have hmono := hf.mono (le_add c i) (hadd c i hc hi)
  exact C_mono_seed s _ _ _ (psi_mono s k _ _ hmono) k (C_mono_argument s _ _ _ hmono k hk)

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem NormalFundamentalSequence.shift {s : OCF.Denis.Supply} {a length : OCF.Denis.O}
    {f : OCF.Denis.O → OCF.Denis.O} (hf : NormalFundamentalSequence s a length f) (c : OCF.Denis.O)
    (hadd : AddPrincipal length) (hc : c < length) (hcRep : Represented s c) :
    NormalFundamentalSequence s a length (fun i => f (c + i)) :=
  ⟨hf.fundamental.shift c hadd hc,
    fun i hi hn => hf.normal _ (hadd c i hc hi) (represented_add s c i hcRep hn)⟩

theorem psi_normal_limit_tail_normalFundamentalSequence (s : OCF.Denis.Supply)
    (k a length c : OCF.Denis.O) (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k)
    (hl : 0 < length) (hadd : AddPrincipal length) (hc : c < length) (hcRep : Represented s c)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s a length f)
    (hbound : a < k) (harg : OCF.Denis.C s a (OCF.Denis.psi s k a) a)
    (hindex : OCF.Denis.C s (f c) (OCF.Denis.psi s k (f c)) k) :
    NormalFundamentalSequence s (OCF.Denis.psi s k a) length
      (fun i => OCF.Denis.psi s k (f (c + i))) := by
  have hshift := hf.shift c hadd hc hcRep
  apply psi_normalFundamentalSequence s k a length hkRep hk hl _ hshift
  · exact OCF.Denis.psi_tail_index_mem s k a length c f hf.fundamental hadd hc hindex
  · intro i hi
    exact OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s k a _ hbound harg
      (hshift.fundamental.below i hi))

/-- The explicit offset succ b works on a domain longer than b,
including uncountable domains. Membership is derived, not assumed at
zero or at all approximants. -/
theorem successor_index_limit_tail_normalFundamentalSequence (s : OCF.Denis.Supply)
    (r b a length : OCF.Denis.O) (hr : Represented s r) (hb : Represented s b)
    (hl : 0 < length) (hadd : AddPrincipal length) (hbl : b < length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : NormalFundamentalSequence s a length f)
    (hbound : a < OCF.Denis.I s r (succ b))
    (harg : OCF.Denis.C s a (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) a) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s r (succ b)) a) length
      (fun i => OCF.Denis.psi s (OCF.Denis.I s r (succ b)) (f (succ b + i))) := by
  have hrank : OCF.Denis.RankBounded s r := by
    obtain ⟨rt, hrt, rfl⟩ := hr
    exact normal_rankBounded s rt hrt
  have hcl := OCF.Denis.succ_lt_limit (hf.fundamental.length_isLimit hl) hbl
  apply psi_normal_limit_tail_normalFundamentalSequence s _ a length (succ b) (Or.inr ⟨r, b, rfl⟩)
    (represented_I s r (succ b) hr (represented_succ s b hb)) hl hadd hcl
    (represented_succ s b hb) f hf hbound harg
  apply (OCF.Denis.C_successor_index_iff_parameter s r b _ hrank).mpr
  exact OCF.Ordinal.lt_trans _ _ _
    (OCF.Ordinal.lt_of_lt_of_le (lt_succ_self b) (hf.fundamental.index_le_value _ hcl))
    (OCF.Denis.psi_argument_normal_below s _ a _ hbound harg (hf.fundamental.below _ hcl))

end
end T.Correspondence.Denis.Covering
