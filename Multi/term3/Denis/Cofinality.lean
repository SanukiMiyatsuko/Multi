import Multi.term3.Denis.Sequences

/-! Intrinsic cofinality of actual limit ordinals. The minimum is taken over
all cofinal maps, not just increasing maps or maps with notation-valued range.
The increasing sequence is constructed afterwards by well-founded recursion.
This does not assert that its values have finite Denis normal forms. -/

namespace OCF.Denis
open Ordinal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

structure CofinalMap (a length : O) (f : O → O) : Prop where
  below : ∀ i, i < length → f i < a
  cofinal : ∀ x, x < a → ∃ i, i < length ∧ x < f i

def HasCofinalMap (a length : O) : Prop := ∃ f, CofinalMap a length f

theorem identity_cofinalMap (a : O) (ha : IsLimit a) :
    CofinalMap a a (fun i => i) :=
  ⟨fun _ hi => hi, fun x hx => ⟨succ x, succ_lt_limit ha hx, lt_succ_self x⟩⟩

def cofinality (a : O) (ha : IsLimit a) : O :=
  least (HasCofinalMap a) ⟨a, fun i => i, identity_cofinalMap a ha⟩

theorem cofinality_spec (a : O) (ha : IsLimit a) :
    HasCofinalMap a (cofinality a ha) ∧
      ∀ b, b < cofinality a ha → ¬ HasCofinalMap a b := least_spec _ _

theorem cofinality_le (a : O) (ha : IsLimit a) {b : O}
    (hb : HasCofinalMap a b) : cofinality a ha ≤ b := least_le _ _ hb

theorem cofinality_le_self (a : O) (ha : IsLimit a) : cofinality a ha ≤ a :=
  cofinality_le a ha ⟨fun i => i, identity_cofinalMap a ha⟩

theorem two_bounded_below_limit {a x y : O} (ha : IsLimit a)
    (hx : x < a) (hy : y < a) : ∃ z, z < a ∧ x < z ∧ y < z := by
  rcases lt_total x y with h | h | h
  · exact ⟨succ y, succ_lt_limit ha hy,
      lt_trans _ _ _ h (lt_succ_self y), lt_succ_self y⟩
  · exact ⟨succ y, succ_lt_limit ha hy, h ▸ lt_succ_self y, lt_succ_self y⟩
  · exact ⟨succ x, succ_lt_limit ha hx, lt_succ_self x,
      lt_trans _ _ _ h (lt_succ_self x)⟩

theorem finite_map_bounded (a : O) (ha : IsLimit a) (n : Nat) (f : O → O)
    (hf : ∀ i, i < finite n → f i < a) :
    ∃ b, b < a ∧ ∀ i, i < finite n → f i < b := by
  induction n with
  | zero => exact ⟨0, (zero_lt_iff_ne_zero a).mpr ha.1,
      fun i hi => False.elim (not_lt_zero i hi)⟩
  | succ n ih =>
    obtain ⟨b, hb, hfb⟩ := ih (fun i hi => hf i (lt_trans _ _ _ hi (lt_succ_self _)))
    obtain ⟨c, hc, hbc, hfc⟩ := two_bounded_below_limit ha hb (hf _ (lt_succ_self _))
    refine ⟨c, hc, fun i hi => ?_⟩
    rcases (lt_succ_iff_le i (finite n)).mp hi with hi | rfl
    · exact lt_trans _ _ _ (hfb i hi) hbc
    · exact hfc

theorem omega_le_cofinality (a : O) (ha : IsLimit a) : omega ≤ cofinality a ha := by
  apply (not_lt_iff_le _ _).mp
  intro h
  obtain ⟨n, hn⟩ := (lt_omega_iff _).mp h
  obtain ⟨f, hf⟩ := (cofinality_spec a ha).1
  rw [hn] at hf
  obtain ⟨b, hb, hfb⟩ := finite_map_bounded a ha n f hf.below
  obtain ⟨i, hi, hbi⟩ := hf.cofinal b hb
  exact lt_asymm hbi (hfb i hi)

theorem short_map_bounded (a : O) (ha : IsLimit a) (b : O)
    (hb : b < cofinality a ha) (f : O → O) (hf : ∀ i, i < b → f i < a) :
    ∃ bound, bound < a ∧ ∀ i, i < b → f i ≤ bound := by
  apply Classical.byContradiction
  intro hn
  apply (cofinality_spec a ha).2 b hb
  refine ⟨f, hf, fun x hx => ?_⟩
  apply Classical.byContradiction
  intro hnx
  apply hn
  refine ⟨x, hx, fun i hi => ?_⟩
  exact (not_lt_iff_le x (f i)).mp (fun h => hnx ⟨i, hi, h⟩)

def cofinalMap (a : O) (ha : IsLimit a) : O → O :=
  Classical.choose (cofinality_spec a ha).1

theorem cofinalMap_spec (a : O) (ha : IsLimit a) :
    CofinalMap a (cofinality a ha) (cofinalMap a ha) :=
  Classical.choose_spec (cofinality_spec a ha).1

private theorem increasing_step_exists (a : O) (ha : IsLimit a) (i : O)
    (hi : i < cofinality a ha) (previous : ∀ j, j < i → {x : O // x < a}) :
    ∃ q, q < a ∧ cofinalMap a ha i ≤ q ∧ ∀ j hj, (previous j hj).val < q := by
  classical
  let g : O → O := fun j => if h : j < i then (previous j h).val else 0
  have hg : ∀ j, j < i → g j < a := by
    intro j hj
    simpa [g, hj] using (previous j hj).property
  obtain ⟨b, hb, hgb⟩ := short_map_bounded a ha i hi g hg
  obtain ⟨q, hq, hbq, hfq⟩ := two_bounded_below_limit ha hb
    ((cofinalMap_spec a ha).below i hi)
  refine ⟨q, hq, Or.inl hfq, fun j hj => ?_⟩
  have hh := lt_of_le_of_lt (hgb j hj) hbq
  simpa [g, hj] using hh

private def increasingPrefix (a : O) (ha : IsLimit a) :
    ∀ i, i < cofinality a ha → {x : O // x < a} :=
  lt_wellFounded.fix (fun i previous hi =>
    let p := increasing_step_exists a ha i hi
      (fun j hj => previous j hj (lt_trans _ _ _ hj hi))
    ⟨Classical.choose p, (Classical.choose_spec p).1⟩)

private theorem increasingPrefix_spec (a : O) (ha : IsLimit a) (i : O)
    (hi : i < cofinality a ha) :
    cofinalMap a ha i ≤ (increasingPrefix a ha i hi).val ∧
      ∀ j hj, (increasingPrefix a ha j (lt_trans _ _ _ hj hi)).val <
        (increasingPrefix a ha i hi).val := by
  unfold increasingPrefix
  rw [WellFounded.fix_eq]
  exact (Classical.choose_spec (increasing_step_exists a ha i hi _)).2

/-- An increasing sequence at the actual cofinality; no normal-form claim. -/
def intrinsicSequence (a : O) (ha : IsLimit a) (i : O) : O :=
  if h : i < cofinality a ha then (increasingPrefix a ha i h).val else 0

theorem intrinsicSequence_spec (a : O) (ha : IsLimit a) :
    TransfiniteFundamentalSequence a (cofinality a ha) (intrinsicSequence a ha) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simpa [intrinsicSequence, hi] using (increasingPrefix a ha i hi).property
  · intro i j hij hj
    have hi := lt_trans _ _ _ hij hj
    simpa [intrinsicSequence, hi, hj] using (increasingPrefix_spec a ha j hj).2 i hij
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (cofinalMap_spec a ha).cofinal x hx
    refine ⟨i, hi, ?_⟩
    have h := lt_of_lt_of_le hxi (increasingPrefix_spec a ha i hi).1
    simpa [intrinsicSequence, hi] using h

def finiteIndex (a : O) : Nat :=
  if h : ∃ n, a = finite n then Classical.choose h else 0

theorem finiteIndex_finite (n : Nat) : finiteIndex (finite n) = n := by
  classical
  have h : ∃ m, finite n = finite m := ⟨n, rfl⟩
  have heq := Classical.choose_spec h
  exact (show finiteIndex (finite n) = Classical.choose h by simp [finiteIndex, h]).trans
    (finite_injective heq).symm

theorem finite_lt_finite_iff (n m : Nat) : finite n < finite m ↔ n < m := by
  constructor
  · intro h
    obtain ⟨k, hk, heq⟩ := (lt_finite_iff _ _).mp h
    exact (finite_injective heq) ▸ hk
  · exact finite_strict

theorem FundamentalSequence.transfinite {a : O} {f : Nat → O}
    (hf : FundamentalSequence a f) :
    TransfiniteFundamentalSequence a omega (fun i => f (finiteIndex i)) := by
  refine ⟨fun _ _ => hf.below _, ?_, ?_⟩
  · intro i j hij hj
    obtain ⟨m, rfl⟩ := (lt_omega_iff j).mp hj
    obtain ⟨n, hn, rfl⟩ := (lt_finite_iff i m).mp hij
    simpa only [finiteIndex_finite] using hf.strict n m hn
  · intro x hx
    obtain ⟨n, hn⟩ := hf.cofinal x hx
    exact ⟨finite n, finite_lt_omega n, by simpa only [finiteIndex_finite] using hn⟩

theorem cofinality_eq_omega_of_fundamentalSequence {a : O} {f : Nat → O}
    (hf : FundamentalSequence a f) : cofinality a hf.isLimit = omega := by
  apply le_antisymm _ (omega_le_cofinality a hf.isLimit)
  exact cofinality_le a hf.isLimit
    ⟨_, hf.transfinite.below, hf.transfinite.cofinal⟩

theorem regular_isLimit {k : O} (hk : UncountableRegular k) : IsLimit k := by
  refine ⟨(zero_lt_iff_ne_zero k).mp (regular_pos hk), ?_⟩
  rintro ⟨b, hb⟩
  have h := regular_succ_lt hk (hb ▸ lt_succ_self b)
  rw [← hb] at h
  exact lt_irrefl _ h

theorem cofinality_regular (k : O) (hk : UncountableRegular k) :
    cofinality k (regular_isLimit hk) = k := by
  apply le_antisymm (cofinality_le_self k _) ((not_lt_iff_le _ _).mp ?_)
  intro h
  obtain ⟨f, hf⟩ := (cofinality_spec k (regular_isLimit hk)).1
  exact regular_no_shorter_cofinal k hk _ h f hf.below hf.cofinal

theorem cofinality_isLimit (a : O) (ha : IsLimit a) : IsLimit (cofinality a ha) := by
  refine ⟨(zero_lt_iff_ne_zero _).mp
    (lt_of_lt_of_le (finite_lt_omega 0) (omega_le_cofinality a ha)), ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨f, hf⟩ := (cofinality_spec a ha).1
  have hfb : f b < a := hf.below b (hb ▸ lt_succ_self b)
  have shorter : HasCofinalMap a b := by
    refine ⟨f, fun i hi => hf.below i (hb ▸ lt_trans _ _ _ hi (lt_succ_self b)), ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy, hfy⟩ := two_bounded_below_limit ha hx hfb
    obtain ⟨i, hi, hyi⟩ := hf.cofinal y hy
    rw [hb, lt_succ_iff_le] at hi
    rcases hi with hi | rfl
    · exact ⟨i, hi, lt_trans _ _ _ hxy hyi⟩
    · exact False.elim (lt_asymm hfy hyi)
  exact (cofinality_spec a ha).2 b (hb ▸ lt_succ_self b) shorter

theorem cofinality_no_shorter_map (a : O) (ha : IsLimit a) (b : O)
    (hb : b < cofinality a ha) : ¬ HasCofinalMap (cofinality a ha) b := by
  rintro ⟨f, hf⟩
  let g := intrinsicSequence a ha
  have hg := intrinsicSequence_spec a ha
  apply (cofinality_spec a ha).2 b hb
  refine ⟨fun i => g (f i), fun i hi => hg.below _ (hf.below i hi), ?_⟩
  intro x hx
  obtain ⟨j, hj, hxj⟩ := hg.cofinal x hx
  obtain ⟨i, hi, hji⟩ := hf.cofinal j hj
  exact ⟨i, hi, lt_trans _ _ _ hxj (hg.strict j (f i) hji (hf.below i hi))⟩

theorem cofinality_idempotent (a : O) (ha : IsLimit a) :
    cofinality (cofinality a ha) (cofinality_isLimit a ha) = cofinality a ha := by
  apply le_antisymm (cofinality_le_self _ _) ((not_lt_iff_le _ _).mp ?_)
  intro h
  exact cofinality_no_shorter_map a ha _ h (cofinality_spec _ _).1

theorem cofinality_uncountableRegular (a : O) (ha : IsLimit a)
    (hu : omega < cofinality a ha) : UncountableRegular (cofinality a ha) := by
  classical
  refine ⟨hu, fun b hb f hf => ?_⟩
  let F : O → O := fun i =>
    if hi : i < b then f (Classical.choose (initial_surjective b i hi)) else 0
  have hF : ∀ i, i < b → F i < cofinality a ha := by
    intro i hi
    simpa [F, hi] using hf (Classical.choose (initial_surjective b i hi))
  have bounded : ∃ c, c < cofinality a ha ∧ ∀ i, i < b → F i ≤ c := by
    apply Classical.byContradiction
    intro hn
    apply cofinality_no_shorter_map a ha b hb
    refine ⟨F, hF, fun x hx => ?_⟩
    apply Classical.byContradiction
    intro hnx
    apply hn
    exact ⟨x, hx, fun i hi => (not_lt_iff_le x (F i)).mp (fun h => hnx ⟨i, hi, h⟩)⟩
  obtain ⟨c, hc, hfc⟩ := bounded
  refine ⟨succ c, succ_lt_limit (cofinality_isLimit a ha) hc, fun i => ?_⟩
  let v := type ((representative b).below i)
  have hv : v < b := initial_lt b i
  have heq : Classical.choose (initial_surjective b v hv) = i := by
    apply initial_injective b
    exact (Classical.choose_spec (initial_surjective b v hv)).symm
  have hh := lt_of_le_of_lt (hfc v hv) (lt_succ_self c)
  simpa [F, hv, heq] using hh

end
end OCF.Denis
