import Multi.term3.Denis.Barrier

/-! Tools for the uniform stage bound.

* `IsoIn s A B x`: `x` is a limit and `C(A, B)` has no element in some
  final interval `[c, x)`.
* `C_canonical`: every element of a closure is zero, a seed, a sum of two
  smaller elements, an `I` value of smaller elements, or a proper collapse.
* `psi_le_sup_of_diagonal` and `stage_iteration`: the diagonal argument of
  `hasCoveringSequence_psi_diagonal`, for an arbitrary argument.
* `sep_mem`: the least collapse value above an element, with arguments from
  a closure `C(e, x)`, lies in every closure containing the element and the
  index whose cutoff exceeds `e` and whose seed is at most `x`.
* `supBelow`: the least strict upper bound of a closure below an ordinal. -/

namespace OCF.Denis
open Ordinal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The larger of two ordinals. -/
def omax (a b : O) : O := if a < b then b else a

theorem le_omax_left (a b : O) : a ≤ omax a b := by
  unfold omax
  split
  · exact Or.inl ‹a < b›
  · exact le_refl _

theorem le_omax_right (a b : O) : b ≤ omax a b := by
  unfold omax
  split
  · exact le_refl _
  · exact (not_lt_iff_le _ _).mp ‹¬ a < b›

theorem omax_cases (a b : O) : omax a b = a ∨ omax a b = b := by
  unfold omax
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `x` is a limit with no element of `C(A, B)` in a final interval below it. -/
def IsoIn (s : Supply) (A B x : O) : Prop :=
  IsLimit x ∧ ∃ c, c < x ∧ ∀ d, C s A B d → c ≤ d → d < x → False

theorem IsoIn.seed_lt {s : Supply} {A B x : O} (h : IsoIn s A B x) : B < x := by
  obtain ⟨_, c, hcx, hc⟩ := h
  apply lt_of_not_ge'
  intro hxB
  exact hc c (C_seed s A B c (lt_of_lt_of_le hcx hxB)) (le_refl c) hcx

theorem IsoIn.index_le {s : Supply} {k A x : O} (h : IsoIn s A (psi s k A) x)
    (hx : C s A (psi s k A) x) : k ≤ x := by
  apply (not_lt_iff_le _ _).mp
  intro hxk
  exact lt_asymm (psi_closed s k A x hx hxk) h.seed_lt

/-- Canonical decomposition of an element of a closure. -/
theorem C_canonical (s : Supply) (A B b : O) (hb : C s A B b) :
    b = 0 ∨ b < B ∨
    (∃ u v, b = u + v ∧ u < b ∧ v < b ∧ C s A B u ∧ C s A B v) ∨
    (∃ r z, b = I s r z ∧ r < b ∧ z < b ∧ C s A B r ∧ C s A B z) ∨
    (∃ k f, b = psi s k f ∧ f < A ∧ ProperCollapse s k f ∧ C s A B k ∧ C s A B f) := by
  have aux (x : O) (hx : PC s A B x) : x = b →
      b = 0 ∨ b < B ∨
      (∃ u v, b = u + v ∧ u < b ∧ v < b ∧ C s A B u ∧ C s A B v) ∨
      (∃ r z, b = I s r z ∧ r < b ∧ z < b ∧ C s A B r ∧ C s A B z) ∨
      (∃ k f, b = psi s k f ∧ f < A ∧ ProperCollapse s k f ∧ C s A B k ∧ C s A B f) := by
    induction hx with
    | zero =>
      intro heq
      exact Or.inl heq.symm
    | seed hx =>
      intro heq
      exact Or.inr (Or.inl (heq ▸ hx))
    | @add u v hu hv ihu ihv =>
      intro heq
      rcases le_add u v with hu' | hu'
      · rcases right_le_add u v with hv' | hv'
        · rw [heq] at hu' hv'
          exact Or.inr (Or.inr (Or.inl ⟨u, v, heq.symm, hu', hv', hu.sub_C, hv.sub_C⟩))
        · exact ihv (hv'.trans heq)
      · exact ihu (hu'.trans heq)
    | @index u v hu hv ihu ihv =>
      intro heq
      rcases rank_le_I s u v with hu' | hu'
      · rcases index_le_I s u v with hv' | hv'
        · rw [heq] at hu' hv'
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, v, heq.symm, hu', hv', hu.sub_C, hv.sub_C⟩)))
        · exact ihv (hv'.trans heq)
      · exact ihu (hu'.trans heq)
    | @collapse k f hf hp hk hf' _ _ =>
      intro heq
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, f, heq.symm, hf, hp, hk.sub_C, hf'.sub_C⟩)))
  exact aux b (properClosureComplete s A B b hb) rfl

theorem I_limit_cofinal (s : Supply) (r z c : O) (hz : IsLimit z) (hc : c < I s r z) :
    ∃ z0, z0 < z ∧ c < I s r z0 := by
  apply Classical.byContradiction
  intro hnot
  apply (not_lt_iff_le _ _).mpr _ hc
  apply I_limit_le_of_forall s r z c hz
  intro z' hz'
  exact (not_lt_iff_le _ _).mp (fun h => hnot ⟨z', hz', h⟩)

/-- An ordinal between `I r w` and `I r z`, `z` a limit, lies in an
interval `[I r z', I r (succ z'))` with `w ≤ z' < z`. -/
theorem I_interval_of_lt (s : Supply) (r w z b : O) (hz : IsLimit z)
    (hlo : I s r w ≤ b) (hb : b < I s r z) :
    ∃ z', w ≤ z' ∧ z' < z ∧ I s r z' ≤ b ∧ b < I s r (succ z') := by
  classical
  have hex : ∃ v, b < I s r v := ⟨z, hb⟩
  have hspec := least_spec _ hex
  have hle : least (fun v => b < I s r v) hex ≤ z := least_le _ hex hb
  generalize least (fun v => b < I s r v) hex = v2 at hspec hle
  have hbelow : ∀ v, v < v2 → I s r v ≤ b := fun v hv => (not_lt_iff_le _ _).mp (hspec.2 v hv)
  have hv0 : v2 ≠ 0 := by
    intro h
    subst h
    exact (not_lt_iff_le _ _).mpr (le_trans (I_mono s r (zero_le w)) hlo) hspec.1
  by_cases hvs : ∃ v1, v2 = succ v1
  · obtain ⟨v1, rfl⟩ := hvs
    refine ⟨v1, ?_, ?_, hbelow v1 (lt_succ_self v1), hspec.1⟩
    · apply (not_lt_iff_le _ _).mp
      intro hv1w
      exact (not_lt_iff_le _ _).mpr (le_trans (I_mono s r ((succ_le_iff_lt _ _).mpr hv1w)) hlo)
        hspec.1
    · rcases hle with h | h
      · exact lt_trans _ _ _ (lt_succ_self v1) h
      · exact False.elim (hz.2 ⟨v1, h.symm⟩)
  · exact False.elim ((not_lt_iff_le _ _).mpr (I_limit_le_of_forall s r v2 b ⟨hv0, hvs⟩ hbelow)
      hspec.1)

theorem psi_limit_cofinal' (s : Supply) (k a y : O) (ha : IsLimit a) (hy : y < psi s k a) :
    ∃ c, c < a ∧ y < psi s k c := by
  apply Classical.byContradiction
  intro hnot
  apply (not_lt_iff_le _ _).mpr _ hy
  apply psi_limit_le s k a y ha
  intro c hc
  exact (not_lt_iff_le _ _).mp (fun hlt => hnot ⟨c, hc, hlt⟩)

/-- The diagonal argument: if each stage closure below the argument is
bounded by the next term, the collapse values along the sequence reach
`psi k a`. -/
theorem psi_le_sup_of_diagonal (s : Supply) (k a : O) (x : Nat → O)
    (hxmono : ∀ n, x n ≤ x (n + 1))
    (hxbound : ∀ n b, C s (x n) (psi s k (x n)) b → b < a → b < x (n + 1)) :
    psi s k a ≤ sup (fun n => psi s k (x n)) := by
  have hmono : ∀ n m, n ≤ m → x n ≤ x m := by
    intro n m hnm
    induction m with
    | zero =>
      have : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst this
      exact le_refl _
    | succ m ih =>
      rcases Nat.lt_or_eq_of_le hnm with h | rfl
      · exact le_trans (ih (Nat.le_of_lt_succ h)) (hxmono m)
      · exact le_refl _
  let v : Nat → O := fun n => psi s k (x n)
  have hvmono : ∀ n m, n ≤ m → v n ≤ v m :=
    fun n m hnm => psi_mono s k _ _ (hmono n m hnm)
  have promote : ∀ n m, n ≤ m → ∀ z, C s (x n) (v n) z → C s (x m) (v m) z :=
    fun n m hnm z hz => C_mono_seed s _ _ _ (hvmono n m hnm) z
      (C_mono_argument s _ _ _ (hmono n m hnm) z hz)
  have combine : ∀ z w, (∃ n, C s (x n) (v n) z) → (∃ n, C s (x n) (v n) w) →
      ∃ n, C s (x n) (v n) z ∧ C s (x n) (v n) w := by
    rintro z w ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, promote n _ (Nat.le_max_left _ _) z hn,
      promote m _ (Nat.le_max_right _ _) w hm⟩
  have hstage : ∀ z, C s a (sup v) z → ∃ n, C s (x n) (v n) z := by
    intro z hz
    apply C_least s a (sup v) (fun z => ∃ n, C s (x n) (v n) z) _ _ _ _ _ z hz
    · exact ⟨0, C_zero s _ _⟩
    · intro z hz
      obtain ⟨n, hn⟩ := (lt_sup_iff v z).mp hz
      exact ⟨n, C_seed s _ _ z hn⟩
    · intro z w hz hw
      obtain ⟨n, hn, hm⟩ := combine z w hz hw
      exact ⟨n, C_add s _ _ z w hn hm⟩
    · intro z w hz hw
      obtain ⟨n, hn, hm⟩ := combine z w hz hw
      exact ⟨n, C_index s _ _ z w hn hm⟩
    · intro j b hb hj hjP hbP
      obtain ⟨n, hn, hm⟩ := combine j b hjP hbP
      exact ⟨n + 1, C_collapse s _ _ j b (hxbound n b hm hb) hj
        (promote n _ (Nat.le_succ n) j hn) (promote n _ (Nat.le_succ n) b hm)⟩
  apply psi_min s k a (sup v)
  refine ⟨(sup_le_iff v k).mpr (fun n => psi_le s k (x n)), ?_⟩
  intro z hz hzk
  obtain ⟨n, hn⟩ := hstage z hz
  exact lt_of_lt_of_le (psi_closed s k (x n) z hn hzk) (le_sup v n)

/-- Iterating a stage bound inside a set `P` gives a sequence whose
collapse values reach `psi k e`. -/
theorem stage_iteration (s : Supply) (k e : O) (P : O → Prop) (h0 : P 0) (he0 : 0 < e)
    (hnext : ∀ z, P z → z < e → ∃ z', P z' ∧ z' < e ∧ z ≤ z' ∧
      ∀ b, C s z (psi s k z) b → b < e → b < z') :
    ∃ x : Nat → O, (∀ n, P (x n) ∧ x n < e) ∧ psi s k e ≤ sup (fun n => psi s k (x n)) := by
  classical
  let Q : O → Prop := fun z => P z ∧ z < e
  let nxt : {z // Q z} → {z // Q z} := fun z =>
    ⟨Classical.choose (hnext z.1 z.2.1 z.2.2),
      (Classical.choose_spec (hnext z.1 z.2.1 z.2.2)).1,
      (Classical.choose_spec (hnext z.1 z.2.1 z.2.2)).2.1⟩
  have hnxt : ∀ z : {z // Q z}, z.1 ≤ (nxt z).1 ∧
      ∀ b, C s z.1 (psi s k z.1) b → b < e → b < (nxt z).1 :=
    fun z => (Classical.choose_spec (hnext z.1 z.2.1 z.2.2)).2.2
  let seq : Nat → {z // Q z} := fun n => Nat.rec ⟨0, h0, he0⟩ (fun _ z => nxt z) n
  have hseq : ∀ n, seq (n + 1) = nxt (seq n) := fun _ => rfl
  have h1 : ∀ n, (seq n).1 ≤ (seq (n + 1)).1 := by
    intro n
    rw [hseq n]
    exact (hnxt (seq n)).1
  have h2 : ∀ n b, C s (seq n).1 (psi s k (seq n).1) b → b < e → b < (seq (n + 1)).1 := by
    intro n b hb hbe
    rw [hseq n]
    exact (hnxt (seq n)).2 b hb hbe
  exact ⟨fun n => (seq n).1, fun n => (seq n).2,
    psi_le_sup_of_diagonal s k e (fun n => (seq n).1) h1 h2⟩

/-- The separation value with arguments from `C(e, x)` lies in every closure
containing the element and the index, with cutoff above `e` and seed at
most `x`. -/
theorem sep_mem (s : Supply) (A' B' e x k m w : O) (he : 0 < e) (heA : e < A') (hB : B' ≤ x)
    (hk : RegularIndex s k) (hkY : C s e x k) (hkZ : C s A' B' k) (hmZ : C s A' B' m)
    (hsep : IsSep s e x k m w) : C s A' B' w := by
  have hctx : CeilCtx s A' B' e x :=
    { below := completeBelow_all s A'
      ca := heA
      bg := hB
      c0 := he
      Q := fun d hd k' hk' hk'P hdP =>
        pcCollapseStep_holds s A' B' k' d (completeBelow_all s A') hk' hk'P hdP
          (lt_trans _ _ _ hd heA) }
  exact ((hctx.inv_all m (properClosureComplete s A' B' m hmZ) 0 m (zero_add m).symm).2 k w hk hkY
    (properClosureComplete s A' B' k hkZ) hsep).sub_C

/-- The least strict upper bound of the elements of `C(A, B)` below `x`. -/
def supBelow (s : Supply) (A B x : O) : O :=
  least (fun t => ∀ d, C s A B d → d < x → d < t) ⟨x, fun _ _ h => h⟩

theorem supBelow_bound (s : Supply) (A B x d : O) (hd : C s A B d) (hdx : d < x) :
    d < supBelow s A B x :=
  (least_spec (fun t => ∀ d, C s A B d → d < x → d < t) ⟨x, fun _ _ h => h⟩).1 d hd hdx

theorem supBelow_le (s : Supply) (A B x t : O) (h : ∀ d, C s A B d → d < x → d < t) :
    supBelow s A B x ≤ t :=
  least_le _ _ h

theorem supBelow_cofinal (s : Supply) (A B x u : O) (hu : u < supBelow s A B x) :
    ∃ d, C s A B d ∧ d < x ∧ u ≤ d := by
  apply Classical.byContradiction
  intro hnot
  apply (least_spec (fun t => ∀ d, C s A B d → d < x → d < t) ⟨x, fun _ _ h => h⟩).2 u hu
  intro d hd hdx
  exact lt_of_not_ge' (fun hud => hnot ⟨d, hd, hdx, hud⟩)

theorem supBelow_addPrincipal (s : Supply) (A B x : O) (hx : AddPrincipal x) :
    AddPrincipal (supBelow s A B x) := by
  intro u v hu hv
  obtain ⟨d1, hd1, hd1x, hud1⟩ := supBelow_cofinal s A B x u hu
  obtain ⟨d2, hd2, hd2x, hvd2⟩ := supBelow_cofinal s A B x v hv
  have hle : u + v ≤ d1 + d2 := le_trans (add_mono_left hud1 v) (add_mono_right d1 hvd2)
  exact lt_of_le_of_lt hle
    (supBelow_bound s A B x _ (C_add s A B d1 d2 hd1 hd2) (hx d1 d2 hd1x hd2x))

end
end OCF.Denis
