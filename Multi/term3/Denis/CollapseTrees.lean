import Multi.term3.Denis.SuccessorRankClosure

/-! Extend closure approximation and diagonal fundamental sequences to
normal trees containing uncountable successor-rank collapse values.
Collapse arguments may be small normal terms, or recursively supported
normal terms below their collapse index. The rank and the argument can
both contain further uncountable collapses. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

def successorRankCollapseTerm (r a : Term) : Term := .psi (.I (succTerm r) .zero) a

theorem denote_successorRankCollapseTerm (s : OCF.Denis.Supply) (r a : Term) :
    denote s (successorRankCollapseTerm r a) =
      OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) (denote s a) := by
  change OCF.Denis.psi s (OCF.Denis.I s (denote s (succTerm r)) 0) (denote s a) = _
  rw [denote_succTerm]

theorem successorRankCollapseTerm_normal_of_mem (s : OCF.Denis.Supply) (r a : Term)
    (hr : IsNormal s r) (ha : IsNormal s a)
    (harg : OCF.Denis.C s (denote s a)
      (OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) (denote s a)) (denote s a)) :
    IsNormal s (successorRankCollapseTerm r a) := by
  have hzero := successorRankZeroTerm_normal s r hr
  cases hzero with
  | collapse hk _ hreg _ =>
    apply IsNormal.collapse hk ha hreg
    change OCF.Denis.C s (denote s a) (denote s (successorRankCollapseTerm r a)) (denote s a)
    rw [denote_successorRankCollapseTerm]
    exact harg

theorem successorRankCollapseTerm_normal (s : OCF.Denis.Supply) (r a : Term)
    (hr : IsNormal s r) (ha : IsNormal s a) (hasmall : denote s a < OCF.Denis.I s 0 0) :
    IsNormal s (successorRankCollapseTerm r a) :=
  successorRankCollapseTerm_normal_of_mem s r a hr ha
    (OCF.Denis.successor_rank_small_argument_mem s _ _ (normal_rankBounded s r hr) hasmall).2

/-- Enlarge an admissible cutoff beyond an already supported
argument, staying below a regular bound and preserving support. -/
theorem admissible_cutoff_above (s : OCF.Denis.Supply) (R c a : OCF.Denis.O)
    (hR : OCF.Denis.UncountableRegular R) (hc : Represented s c) (ha : Represented s a)
    (hcR : c < R) (haR : a < R)
    (hcc : OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) c)
    (hac : OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) a) :
    ∃ d, Represented s d ∧ d < R ∧ a < d ∧ c ≤ d ∧
      OCF.Denis.C s d (OCF.Denis.psi s (OCF.Denis.I s 0 0) d) d := by
  have hex : ∃ e, Represented s e ∧ e < R ∧ a ≤ e ∧ c ≤ e ∧
      OCF.Denis.C s e (OCF.Denis.psi s (OCF.Denis.I s 0 0) e) e := by
    rcases OCF.Ordinal.lt_total a c with h | h | h
    · exact ⟨c, hc, hcR, Or.inl h, le_refl c, hcc⟩
    · exact ⟨c, hc, hcR, Or.inr h, le_refl c, hcc⟩
    · exact ⟨a, ha, haR, le_refl a, Or.inl h,
        OCF.Denis.C_mono_seed s a _ _ (OCF.Denis.psi_mono s _ c a (Or.inl h)) a
          (OCF.Denis.C_mono_argument s c a _ (Or.inl h) a hac)⟩
  obtain ⟨e, he, heR, hae, hce, heC⟩ := hex
  exact ⟨succ e, represented_succ s e he, OCF.Denis.regular_succ_lt hR heR,
    OCF.Ordinal.lt_of_le_of_lt hae (lt_succ_self e),
    OCF.Ordinal.le_trans hce (Or.inl (lt_succ_self e)), OCF.Denis.C_first_successor_argument s e heC⟩

theorem normalApproximation_successorRankCollapse_below (s : OCF.Denis.Supply) (R r a : OCF.Denis.O)
    (hR : OCF.Denis.UncountableRegular R) (ha : Represented s a) (haR : a < R)
    (hr : NormalApproximation s R r) (haC : NormalApproximation s R a) :
    NormalApproximation s R (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) := by
  obtain ⟨c, hc, hcR, hcc, hcr, hca⟩ := normalApproximation_pair s R r a hr haC
  obtain ⟨d, hd, hdR, had, hcd, hdd⟩ := admissible_cutoff_above s R c a hR hc ha hcR haR hcc hca
  have promote (x : OCF.Denis.O) (hx : OCF.Denis.C s c (OCF.Denis.psi s (OCF.Denis.I s 0 0) c) x) :
      OCF.Denis.C s d (OCF.Denis.psi s (OCF.Denis.I s 0 0) d) x :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ c d hcd) x
      (OCF.Denis.C_mono_argument s c d _ hcd x hx)
  have hdpos := OCF.Ordinal.lt_of_le_of_lt (zero_le a) had
  have hsucc := OCF.Denis.C_add s d (OCF.Denis.psi s (OCF.Denis.I s 0 0) d) r (succ 0)
    (promote r hcr) (OCF.Denis.C_finite s d _ hdpos 1)
  rw [add_succ, add_zero] at hsucc
  have hindex := OCF.Denis.C_index s d _ (succ r) 0 hsucc (OCF.Denis.C_zero s d _)
  exact ⟨d, hd, hdR, hdd, OCF.Denis.C_collapse s d _ _ a had
    (Or.inl ⟨succ r, rfl⟩) hindex (promote a hca)⟩

theorem normalApproximation_successorRankCollapse (s : OCF.Denis.Supply) (R r a : OCF.Denis.O)
    (hR : OCF.Denis.UncountableRegular R) (ha : Represented s a) (hasmall : a < OCF.Denis.I s 0 0)
    (hr : NormalApproximation s R r) (haC : NormalApproximation s R a) :
    NormalApproximation s R (OCF.Denis.psi s (OCF.Denis.I s (succ r) 0) a) :=
  normalApproximation_successorRankCollapse_below s R r a hR ha
    (OCF.Ordinal.lt_of_lt_of_le hasmall (by
      rw [OCF.Denis.I_zero]
      exact OCF.Denis.first_le s 0 R ((OCF.Denis.inaccessible_zero_iff R).mpr hR))) hr haC

/-- This includes the earlier IndexTree family and permits recursively
nested successor-rank collapses with admissible arguments below their
index, including uncountable arguments. It is a proved
family, not a redefinition or restriction of IsNormal. -/
inductive CollapseTree (s : OCF.Denis.Supply) : Term → Prop where
  | small {t : Term} : IsNormal s t → denote s t < OCF.Denis.I s 0 0 → CollapseTree s t
  | index {r b : Term} : CollapseTree s r → CollapseTree s b → IsNormal s (.I r b) → CollapseTree s (.I r b)
  | sum {a b : Term} : CollapseTree s a → CollapseTree s b → IsNormal s (.add a b) → CollapseTree s (.add a b)
  | collapse {r a : Term} : CollapseTree s r → IsNormal s a → denote s a < OCF.Denis.I s 0 0 →
      CollapseTree s (successorRankCollapseTerm r a)
  | collapseBelow {r a : Term} : CollapseTree s r → CollapseTree s a →
      denote s a < OCF.Denis.I s (succ (denote s r)) 0 →
      OCF.Denis.C s (denote s a)
        (OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) (denote s a)) (denote s a) →
      CollapseTree s (successorRankCollapseTerm r a)

theorem CollapseTree.normal {s : OCF.Denis.Supply} {t : Term} (ht : CollapseTree s t) : IsNormal s t := by
  induction ht with
  | small ht _ | index _ _ ht | sum _ _ ht => exact ht
  | collapse _ ha hasmall ih => exact successorRankCollapseTerm_normal s _ _ ih ha hasmall
  | collapseBelow _ _ _ harg ihr iha => exact successorRankCollapseTerm_normal_of_mem s _ _ ihr iha harg

theorem IndexTree.collapseTree {s : OCF.Denis.Supply} {t : Term} (ht : IndexTree s t) : CollapseTree s t := by
  induction ht with
  | small ht hsmall => exact .small ht hsmall
  | index _ _ ht ihr ihb => exact .index ihr ihb ht
  | sum _ _ ht iha ihb => exact .sum iha ihb ht

theorem CollapseTree.approximation {s : OCF.Denis.Supply} {t : Term} (ht : CollapseTree s t)
    (R : OCF.Denis.O) (hR : OCF.Denis.UncountableRegular R)
    (hC : OCF.Denis.C s R (OCF.Denis.psi s (OCF.Denis.I s 0 0) R) (denote s t)) :
    NormalApproximation s R (denote s t) := by
  induction ht with
  | @small t ht hsmall =>
    have hlt := OCF.Denis.psi_closed s _ _ _ hC hsmall
    obtain ⟨c, hc, hcR, htc, hcc⟩ := normal_interpolation s R hR t ht hlt
    exact ⟨c, hc, hcR, hcc, OCF.Denis.C_seed s _ _ _ htc⟩
  | @index p b hp hb ht ihp ihb =>
    cases ht with
    | index hpn hbn hpl hbl =>
      obtain ⟨hpC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ (denote s p) (denote s b) hpl hbl hC
      obtain ⟨c, hc, hcR, hcc, hcp, hcb⟩ := normalApproximation_pair s R _ _ (ihp hpC) (ihb hbC)
      exact ⟨c, hc, hcR, hcc, OCF.Denis.C_index s _ _ _ _ hcp hcb⟩
  | @sum a b ha hb ht iha ihb =>
    obtain ⟨haC, hbC⟩ := C_normal_sum_components s _ _ a b ht hC
    obtain ⟨c, hc, hcR, hcc, hca, hcb⟩ := normalApproximation_pair s R _ _ (iha haC) (ihb hbC)
    exact ⟨c, hc, hcR, hcc, OCF.Denis.C_add s _ _ _ _ hca hcb⟩
  | @collapse r a hr ha hasmall ihr =>
    rw [denote_successorRankCollapseTerm] at hC ⊢
    obtain ⟨hrC, haC⟩ := OCF.Denis.C_successor_rank_small_parameters s _ _ R _
      (normal_rankBounded s r hr.normal) hasmall hC
    have harg := (IndexTree.small ha hasmall).approximation R hR haC
    exact normalApproximation_successorRankCollapse s R _ _ hR ⟨a, ha, rfl⟩ hasmall (ihr hrC) harg
  | @collapseBelow r a hr ha habound harg ihr iha =>
    rw [denote_successorRankCollapseTerm] at hC ⊢
    have hrank := normal_rankBounded s r hr.normal
    obtain ⟨hrC, haC⟩ := OCF.Denis.C_successor_rank_below_parameters s _ _ R _ hrank habound harg hC
    have hseed : OCF.Denis.psi s (OCF.Denis.I s 0 0) R <
        OCF.Denis.psi s (OCF.Denis.I s (succ (denote s r)) 0) (denote s a) :=
      OCF.Ordinal.lt_trans _ _ _ (OCF.Denis.psi_lt s _ R (OCF.Denis.first_regular s))
        (OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.first_lt_successor_rank_zero s _ hrank)
          (OCF.Denis.psi_mono s _ 0 (denote s a) (zero_le _)))
    have haR := OCF.Denis.C_collapse_argument_lt s R _ _ _ (Or.inl ⟨succ (denote s r), rfl⟩)
      (Or.inl hseed) hC
    exact normalApproximation_successorRankCollapse_below s R _ _ hR ⟨a, ha.normal, rfl⟩ haR (ihr hrC) (iha haC)

theorem collapseTree_diagonal_dense (s : OCF.Denis.Supply) (t : Term) (ht : CollapseTree s t)
    (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) := by
  rcases OCF.Denis.regularIndex_lower_bound s _ hreg with hlarge | heq
  · obtain ⟨c, hc, hcr, hcc, hct⟩ := ht.approximation _ (OCF.Denis.regularIndex_regular s _ hreg) harg
    exact seeded_diagonal_dense s _ c ⟨t, ht.normal, rfl⟩ hc hreg hlarge ⟨hcr, hcc, hct⟩
  · rw [← heq]
    exact epsilon_dense s

theorem revised_collapseTree_diagonal_fundamentalSequence (s : OCF.Denis.Supply)
    (t : Term) (ht : CollapseTree s t) (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))) :=
  revised_fundamentalSequence_of_dense s _
    (OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.first_regular s)))
    (collapseTree_diagonal_dense s t ht hreg harg)

theorem revised_collapseTree_diagonal_normalFundamentalSequence (s : OCF.Denis.Supply)
    (t : Term) (ht : CollapseTree s t) (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    NormalFundamentalSequence s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) OCF.Denis.omega
      (fun i => revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))
        (OCF.Denis.finiteIndex i)) :=
  ⟨(revised_collapseTree_diagonal_fundamentalSequence s t ht hreg harg).transfinite,
    fun _ _ _ => revisedValue_represented s _ _⟩

theorem collapseTree_diagonal_cofinality (s : OCF.Denis.Supply)
    (t : Term) (ht : CollapseTree s t) (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    OCF.Denis.cofinality (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))
      (revised_collapseTree_diagonal_fundamentalSequence s t ht hreg harg).isLimit = OCF.Denis.omega :=
  OCF.Denis.cofinality_eq_omega_of_fundamentalSequence
    (revised_collapseTree_diagonal_fundamentalSequence s t ht hreg harg)

theorem revised_normalized_collapseTree_diagonal_fundamentalSequence (s : OCF.Denis.Supply)
    (t : Term) (ht : CollapseTree s (Nested.normalize s t))
    (hreg : OCF.Denis.RegularIndex s (denote s t))
    (harg : OCF.Denis.C s (denote s t) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t)) (denote s t)) :
    OCF.Denis.FundamentalSequence (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))
      (revisedValue s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s t))) := by
  have hnreg : OCF.Denis.RegularIndex s (denote s (Nested.normalize s t)) := by
    rwa [Nested.denote_normalize]
  have hnarg : OCF.Denis.C s (denote s (Nested.normalize s t))
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (denote s (Nested.normalize s t)))
      (denote s (Nested.normalize s t)) := by rwa [Nested.denote_normalize]
  have h := revised_collapseTree_diagonal_fundamentalSequence s _ ht hnreg hnarg
  rwa [Nested.denote_normalize] at h

end
end T.Correspondence.Denis.Covering
