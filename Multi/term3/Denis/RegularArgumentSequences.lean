import Multi.term3.Denis.ProperLimitCofinality

/-! Proper collapses at a regular argument R >= k. Iteration of psi_R
from zero gives a countable diagonal. The parent's closure membership
provides a finite tail on which every term is normal for psi_k. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_bounded_of_postfixed_le (s : Supply) (k a c : O)
    (hc : c ≤ k) (hpa : psi s k a ≤ a) : psi s k c ≤ psi s k a := by
  have lift (x : O) (hx : C s c (psi s k a) x) : C s a (psi s k a) x := by
    apply C_least s c (psi s k a) (C s a (psi s k a)) _ _ _ _ _ x hx
    · exact C_zero s _ _
    · exact fun x hx => C_seed s _ _ x hx
    · exact fun x y hx hy => C_add s _ _ x y hx hy
    · exact fun x y hx hy => C_index s _ _ x y hx hy
    · intro j b hb hj hk harg
      have hba := lt_of_lt_of_le (psi_closed s k a b harg (lt_of_lt_of_le hb hc)) hpa
      exact C_collapse s a _ j b hba hj hk harg
  exact psi_min s k c (psi s k a) ⟨psi_le s k a,
    fun x hx hxk => psi_closed s k a x (lift x hx) hxk⟩

def regularArgumentIter (s : Supply) (r : O) : Nat → O := seededIter s r 0

theorem regularArgumentIter_le_next (s : Supply) (r : O) (n : Nat) :
    regularArgumentIter s r n ≤ regularArgumentIter s r (n + 1) := by
  induction n with
  | zero => exact zero_le _
  | succ n ih => exact psi_mono s r _ _ ih

theorem regularArgumentIter_mono (s : Supply) (r : O) {n m : Nat} (h : n ≤ m) :
    regularArgumentIter s r n ≤ regularArgumentIter s r m := by
  induction m with
  | zero => have hn := Nat.eq_zero_of_le_zero h; subst n; exact le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact le_trans (ih (Nat.le_of_lt_succ h)) (regularArgumentIter_le_next s r m)
    · subst n; exact le_refl _

theorem regularArgumentIter_below (s : Supply) (r : O) (hr : RegularIndex s r) (n : Nat) :
    regularArgumentIter s r n < r := by
  cases n with
  | zero => exact regular_pos (regularIndex_regular s r hr)
  | succ n => exact psi_lt s r _ (regularIndex_regular s r hr)

theorem regularArgumentIter_mem (s : Supply) (r seed : O) (hr : RegularIndex s r)
    (hR : C s r seed r) (n : Nat) : C s r seed (regularArgumentIter s r n) := by
  induction n with
  | zero => exact C_zero s _ _
  | succ n ih => exact C_collapse s _ _ r _ (regularArgumentIter_below s r hr n) hr hR ih

theorem regularArgumentIter_strict (s : Supply) (r : O) (hr : RegularIndex s r)
    (hR : C s r (psi s r r) r) {n m : Nat} (h : n < m) :
    regularArgumentIter s r n < regularArgumentIter s r m := by
  have hstep (n : Nat) : regularArgumentIter s r n < regularArgumentIter s r (n + 1) := by
    apply Classical.byContradiction
    intro hn
    have hpost := (not_lt_iff_le _ _).mp hn
    have hb := psi_bounded_of_postfixed_le s r (regularArgumentIter s r n) r (le_refl r) hpost
    have hparent : regularArgumentIter s r n < psi s r r := psi_closed s r r _
      (regularArgumentIter_mem s r _ hr hR n) (regularArgumentIter_below s r hr n)
    exact lt_irrefl _ (lt_of_lt_of_le hparent (le_trans hb hpost))
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact lt_trans _ _ _ (ih h) (hstep m)
    · exact hstep n

def regularArgumentSeq (s : Supply) (k r : O) (n : Nat) : O :=
  psi s k (regularArgumentIter s r n)

theorem regularArgumentSeq_mono (s : Supply) (k r : O) {n m : Nat} (h : n ≤ m) :
    regularArgumentSeq s k r n ≤ regularArgumentSeq s k r m :=
  psi_mono s k _ _ (regularArgumentIter_mono s r h)

theorem C_regularArgument_sup (s : Supply) (k r : O) (hkr : k ≤ r)
    (x : O) (hx : C s r (sup (regularArgumentSeq s k r)) x) :
    ∃ n, C s (regularArgumentIter s r n) (regularArgumentSeq s k r n) x := by
  let f := regularArgumentIter s r
  let g := regularArgumentSeq s k r
  have promote (n m : Nat) (hnm : n ≤ m) (x : O) (hx : C s (f n) (g n) x) : C s (f m) (g m) x :=
    C_mono_seed s _ _ _ (regularArgumentSeq_mono s k r hnm) x
      (C_mono_argument s _ _ _ (regularArgumentIter_mono s r hnm) x hx)
  have combine (x y : O) (hx : ∃ n, C s (f n) (g n) x) (hy : ∃ n, C s (f n) (g n) y) :
      ∃ n, C s (f n) (g n) x ∧ C s (f n) (g n) y := by
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m, promote n _ (Nat.le_max_left _ _) x hn, promote m _ (Nat.le_max_right _ _) y hm⟩
  apply C_least s r (sup g) (fun x => ∃ n, C s (f n) (g n) x) _ _ _ _ _ x hx
  · exact ⟨0, C_zero s _ _⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (lt_sup_iff g x).mp hx
    exact ⟨n, C_seed s _ _ x hn⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_add s _ _ x y hn hm⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_index s _ _ x y hn hm⟩
  · intro j b hb hj hx hy
    obtain ⟨n, hn, hm⟩ := combine j b hx hy
    have hb' : b < f (n + 1) := psi_closed s r (f n) b
      (C_mono_seed s _ _ _ (psi_mono_index s k r (f n) hkr) b hm) hb
    exact ⟨n + 1, C_collapse s _ _ j b hb' hj
      (promote n _ (Nat.le_succ n) j hn) (promote n _ (Nat.le_succ n) b hm)⟩

theorem regularArgumentSeq_sup (s : Supply) (k r : O) (hr : RegularIndex s r) (hkr : k ≤ r) :
    sup (regularArgumentSeq s k r) = psi s k r := by
  apply le_antisymm
  · exact (sup_le_iff _ _).mpr (fun n => psi_mono s k _ r (Or.inl (regularArgumentIter_below s r hr n)))
  · apply psi_min
    refine ⟨(sup_le_iff _ _).mpr (fun n => psi_le s k _), ?_⟩
    intro x hx hxk
    obtain ⟨n, hn⟩ := C_regularArgument_sup s k r hkr x hx
    exact lt_of_lt_of_le (psi_closed s k _ x hn hxk) (le_sup _ n)

theorem regularArgumentSeq_below (s : Supply) (k r : O) (hk : RegularIndex s k) (hr : RegularIndex s r)
    (hK : C s r (psi s k r) k) (hR : C s r (psi s k r) r) (n : Nat) :
    regularArgumentSeq s k r n < psi s k r :=
  psi_closed s k r _ (C_collapse s _ _ k _ (regularArgumentIter_below s r hr n) hk hK
    (regularArgumentIter_mem s r _ hr hR n)) (psi_lt s k _ (regularIndex_regular s k hk))

theorem regularArgumentIter_mem_at_stage (s : Supply) (k r : O) (hr : RegularIndex s r)
    (hR : C s r (psi s r r) r) (n : Nat)
    (hstage : C s (regularArgumentIter s r n) (regularArgumentSeq s k r n) r) :
    C s (regularArgumentIter s r n) (regularArgumentSeq s k r n) (regularArgumentIter s r n) := by
  have aux (m : Nat) (hm : m ≤ n) :
      C s (regularArgumentIter s r n) (regularArgumentSeq s k r n) (regularArgumentIter s r m) := by
    induction m with
    | zero => exact C_zero s _ _
    | succ m ih =>
      exact C_collapse s _ _ r _ (regularArgumentIter_strict s r hr hR (Nat.lt_of_succ_le hm)) hr hstage
        (ih (Nat.le_trans (Nat.le_succ m) hm))
  exact aux n (Nat.le_refl n)

theorem regularArgument_tail (s : Supply) (k r : O) (hk : RegularIndex s k) (hr : RegularIndex s r)
    (hkr : k ≤ r) (hK : C s r (psi s k r) k) (hR : C s r (psi s k r) r) :
    ∃ N, FundamentalSequence (psi s k r) (fun n => regularArgumentSeq s k r (n + N)) ∧
      ∀ n, C s (regularArgumentIter s r (n + N)) (regularArgumentSeq s k r (n + N))
        (regularArgumentIter s r (n + N)) := by
  have hRself := C_mono_seed s r _ _ (psi_mono_index s k r r hkr) r hR
  have hK' : C s r (sup (regularArgumentSeq s k r)) k := by rw [regularArgumentSeq_sup s k r hr hkr]; exact hK
  have hR' : C s r (sup (regularArgumentSeq s k r)) r := by rw [regularArgumentSeq_sup s k r hr hkr]; exact hR
  obtain ⟨NK, hNK⟩ := C_regularArgument_sup s k r hkr k hK'
  obtain ⟨NR, hNR⟩ := C_regularArgument_sup s k r hkr r hR'
  let N := max NK NR
  have promote (j n : Nat) (hjn : j ≤ n + N) (x : O)
      (hx : C s (regularArgumentIter s r j) (regularArgumentSeq s k r j) x) :
      C s (regularArgumentIter s r (n + N)) (regularArgumentSeq s k r (n + N)) x :=
    C_mono_seed s _ _ _ (regularArgumentSeq_mono s k r hjn) x
      (C_mono_argument s _ _ _ (regularArgumentIter_mono s r hjn) x hx)
  have hKn (n : Nat) := promote NK n (by dsimp [N]; omega) k hNK
  have hRn (n : Nat) := promote NR n (by dsimp [N]; omega) r hNR
  have harg (n : Nat) := regularArgumentIter_mem_at_stage s k r hr hRself (n + N) (hRn n)
  refine ⟨N, ⟨fun n => regularArgumentSeq_below s k r hk hr hK hR (n + N), ?_, ?_⟩, harg⟩
  · intro n m hnm
    exact psi_strict_of_mem s k _ _ hk
      (regularArgumentIter_strict s r hr hRself (by omega)) (hKn n) (harg n)
  · intro x hx
    rw [← regularArgumentSeq_sup s k r hr hkr, lt_sup_iff] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, lt_of_lt_of_le hn (regularArgumentSeq_mono s k r (Nat.le_add_right n N))⟩

theorem regularArgument_isLimit (s : Supply) (k r : O) (hk : RegularIndex s k) (hr : RegularIndex s r)
    (hkr : k ≤ r) (hK : C s r (psi s k r) k) (hR : C s r (psi s k r) r) :
    IsLimit (psi s k r) := by
  obtain ⟨_, hf, _⟩ := regularArgument_tail s k r hk hr hkr hK hR
  exact hf.isLimit

theorem regularArgument_cofinality (s : Supply) (k r : O) (hk : RegularIndex s k) (hr : RegularIndex s r)
    (hkr : k ≤ r) (hK : C s r (psi s k r) k) (hR : C s r (psi s k r) r) :
    cofinality (psi s k r) (regularArgument_isLimit s k r hk hr hkr hK hR) = omega := by
  obtain ⟨_, hf, _⟩ := regularArgument_tail s k r hk hr hkr hK hR
  exact cofinality_eq_omega_of_fundamentalSequence hf

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem regularArgumentIter_represented (s : OCF.Denis.Supply) (r : OCF.Denis.O)
    (hr : OCF.Denis.RegularIndex s r) (hrRep : Represented s r)
    (hR : OCF.Denis.C s r (OCF.Denis.psi s r r) r) (n : Nat) :
    Represented s (OCF.Denis.regularArgumentIter s r n) := by
  induction n with
  | zero => exact ⟨.zero, .zero, rfl⟩
  | succ n ih =>
    exact represented_psi_of_mem s r _ hrRep ih hr (OCF.Denis.C_seed s _ _ _
      (OCF.Denis.regularArgumentIter_strict s r hr hR (Nat.lt_succ_self n)))

/-- Every proper normal collapse at a regular argument at least its
index has a normal countable fundamental sequence. All seed conditions
are derived from the parent. -/
theorem proper_regular_argument_dense (s : OCF.Denis.Supply) (k r : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hr : OCF.Denis.RegularIndex s r)
    (hkRep : Represented s k) (hrRep : Represented s r) (hkr : k ≤ r)
    (hK : OCF.Denis.C s r (OCF.Denis.psi s k r) k) (hR : OCF.Denis.C s r (OCF.Denis.psi s k r) r) :
    DenseBelow s (OCF.Denis.psi s k r) := by
  obtain ⟨N, hf, harg⟩ := OCF.Denis.regularArgument_tail s k r hk hr hkr hK hR
  apply dense_of_normal_sequence s _ _ hf
  intro n
  exact represented_psi_of_mem s k _ hkRep
    (regularArgumentIter_represented s r hr hrRep
      (OCF.Denis.C_mono_seed s r _ _ (OCF.Denis.psi_mono_index s k r r hkr) r hR) (n + N)) hk (harg n)

end
end T.Correspondence.Denis.Covering
