import Multi.term3.Denis.Cofinality

/-! Ordinal-indexed continuity rules. These use the original C, I and psi;
normality premises for a psi branch are explicit, rather than assumed. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def indexedSup (length : O) (f : O → O) : O :=
  sup (fun i : (representative length).Carrier => f (type ((representative length).below i)))

theorem lt_indexedSup_iff (length : O) (f : O → O) (x : O) :
    x < indexedSup length f ↔ ∃ i, i < length ∧ x < f i := by
  rw [indexedSup, lt_sup_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, initial_lt length i, hi⟩
  · rintro ⟨i, hi, hxi⟩
    obtain ⟨j, hj⟩ := initial_surjective length i hi
    exact ⟨j, hj ▸ hxi⟩

theorem le_indexedSup (length : O) (f : O → O) {i : O} (hi : i < length) :
    f i ≤ indexedSup length f := by
  obtain ⟨j, hj⟩ := initial_surjective length i hi
  exact hj ▸ le_sup _ j

theorem indexedSup_le (length : O) (f : O → O) (a : O)
    (hf : ∀ i, i < length → f i ≤ a) : indexedSup length f ≤ a :=
  (sup_le_iff _ _).mpr (fun i => hf _ (initial_lt length i))

theorem TransfiniteFundamentalSequence.mono {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) {i j : O}
    (hij : i ≤ j) (hj : j < length) : f i ≤ f j := by
  rcases hij with hij | rfl
  · exact Or.inl (hf.strict i j hij hj)
  · exact le_refl _

theorem TransfiniteFundamentalSequence.sup_eq {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) : indexedSup length f = a := by
  apply le_antisymm (indexedSup_le _ _ _ (fun i hi => Or.inl (hf.below i hi)))
  apply (not_lt_iff_le _ _).mp
  intro h
  obtain ⟨i, hi, hxi⟩ := hf.cofinal _ h
  exact lt_irrefl _ (lt_of_lt_of_le hxi (le_indexedSup _ _ hi))

theorem TransfiniteFundamentalSequence.isLimit {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (hl : 0 < length) : IsLimit a := by
  constructor
  · intro hz
    exact not_lt_zero _ (hz ▸ hf.below 0 hl)
  · rintro ⟨b, hb⟩
    obtain ⟨i, hi, hbi⟩ := hf.cofinal b (hb ▸ lt_succ_self b)
    have hia := hf.below i hi
    rw [hb, lt_succ_iff_le] at hia
    exact lt_irrefl _ (lt_of_lt_of_le hbi hia)

theorem TransfiniteFundamentalSequence.length_isLimit {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (hl : 0 < length) : IsLimit length := by
  refine ⟨(zero_lt_iff_ne_zero length).mp hl, ?_⟩
  rintro ⟨b, hb⟩
  have hbl : b < length := hb ▸ lt_succ_self b
  obtain ⟨i, hi, hbi⟩ := hf.cofinal (f b) (hf.below b hbl)
  rw [hb, lt_succ_iff_le] at hi
  exact lt_irrefl _ (lt_of_lt_of_le hbi (hf.mono hi hbl))

theorem TransfiniteFundamentalSequence.pullback {a length b : O} {f g : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (hg : CofinalMap a b g) :
    HasCofinalMap length b := by
  classical
  let h : O → O := fun i => if hi : i < b then
    Classical.choose (hf.cofinal (g i) (hg.below i hi)) else 0
  have hs (i : O) (hi : i < b) : h i < length ∧ g i < f (h i) := by
    simpa [h, hi] using Classical.choose_spec (hf.cofinal (g i) (hg.below i hi))
  refine ⟨h, fun i hi => (hs i hi).1, fun x hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ := hg.cofinal (f x) (hf.below x hx)
  refine ⟨i, hi, ?_⟩
  rcases lt_total x (h i) with hh | hh | hh
  · exact hh
  · have hbad := lt_trans _ _ _ hxi (hs i hi).2
    rw [hh] at hbad
    exact False.elim (lt_irrefl _ hbad)
  · exact False.elim (lt_irrefl _
      (lt_trans _ _ _ (lt_trans _ _ _ hxi (hs i hi).2) (hf.strict _ _ hh hx)))

theorem cofinality_eq_of_transfiniteFundamentalSequence {a length : O} {f : O → O}
    (hf : TransfiniteFundamentalSequence a length f) (hl : 0 < length) :
    cofinality a (hf.isLimit hl) = cofinality length (hf.length_isLimit hl) := by
  let hlength := hf.length_isLimit hl
  have hg := intrinsicSequence_spec length hlength
  apply le_antisymm
  · apply cofinality_le a (hf.isLimit hl)
    refine ⟨fun i => f (intrinsicSequence length hlength i),
      fun i hi => hf.below _ (hg.below i hi), ?_⟩
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hf.cofinal x hx
    obtain ⟨i, hi, hji⟩ := hg.cofinal j hj
    exact ⟨i, hi, lt_trans _ _ _ hxj (hf.strict _ _ hji (hg.below i hi))⟩
  · exact cofinality_le length hlength (hf.pullback (cofinalMap_spec a (hf.isLimit hl)))

/-- A valid sequence indexed by a cofinality has the minimum possible length. -/
theorem cofinality_eq_of_minimal_length {a b : O} (hb : IsLimit b) {f : O → O}
    (hf : TransfiniteFundamentalSequence a (cofinality b hb) f) :
    cofinality a (hf.isLimit
      (lt_of_lt_of_le (finite_lt_omega 0) (omega_le_cofinality b hb))) = cofinality b hb := by
  have hl := lt_of_lt_of_le (finite_lt_omega 0) (omega_le_cofinality b hb)
  exact (cofinality_eq_of_transfiniteFundamentalSequence hf hl).trans (cofinality_idempotent b hb)

theorem I_transfiniteFundamentalSequence (s : Supply) (r a length : O) (f : O → O)
    (hl : 0 < length) (hf : TransfiniteFundamentalSequence a length f) :
    TransfiniteFundamentalSequence (I s r a) length (fun i => I s r (f i)) := by
  refine ⟨fun i hi => I_strict s r (hf.below i hi),
    fun i j hij hj => I_strict s r (hf.strict i j hij hj), ?_⟩
  intro x hx
  rw [I_limit s r a (hf.isLimit hl).1 (hf.isLimit hl).2, lt_sup_iff] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨i, hi, hyi⟩ := hf.cofinal _ (initial_lt a y)
  exact ⟨i, hi, lt_trans _ _ _ hy (I_strict s r hyi)⟩

theorem add_transfiniteFundamentalSequence (b a length : O) (f : O → O)
    (hl : 0 < length) (hf : TransfiniteFundamentalSequence a length f) :
    TransfiniteFundamentalSequence (b + a) length (fun i => b + f i) := by
  refine ⟨fun i hi => add_lt_add_right b (hf.below i hi),
    fun i j hij hj => add_lt_add_right b (hf.strict i j hij hj), ?_⟩
  intro x hx
  rcases (lt_add_iff b a x).mp hx with hxb | ⟨y, hy, hxy⟩
  · exact ⟨0, hl, lt_of_lt_of_le hxb (le_add b (f 0))⟩
  · obtain ⟨i, hi, hyi⟩ := hf.cofinal y hy
    exact ⟨i, hi, lt_of_le_of_lt hxy (add_lt_add_right b hyi)⟩

theorem C_directed_indexedSup (s : Supply) (length : O) (hl : 0 < length) (f g : O → O)
    (hf : ∀ i j, i ≤ j → j < length → f i ≤ f j)
    (hg : ∀ i j, i ≤ j → j < length → g i ≤ g j)
    (x : O) (hx : C s (indexedSup length f) (indexedSup length g) x) :
    ∃ i, i < length ∧ C s (f i) (g i) x := by
  have promote (i j : O) (hij : i ≤ j) (hj : j < length) (x : O)
      (hx : C s (f i) (g i) x) : C s (f j) (g j) x :=
    C_mono_seed s _ _ _ (hg i j hij hj) x
      (C_mono_argument s _ _ _ (hf i j hij hj) x hx)
  have combine (x y : O) (hx : ∃ i, i < length ∧ C s (f i) (g i) x)
      (hy : ∃ i, i < length ∧ C s (f i) (g i) y) :
      ∃ i, i < length ∧ C s (f i) (g i) x ∧ C s (f i) (g i) y := by
    obtain ⟨i, hi, hix⟩ := hx
    obtain ⟨j, hj, hjy⟩ := hy
    rcases lt_total i j with hij | hij | hji
    · exact ⟨j, hj, promote i j (Or.inl hij) hj x hix, hjy⟩
    · exact ⟨j, hj, hij ▸ hix, hjy⟩
    · exact ⟨i, hi, hix, promote j i (Or.inl hji) hi y hjy⟩
  apply C_least s _ _ (fun x => ∃ i, i < length ∧ C s (f i) (g i) x) _ _ _ _ _ x hx
  · exact ⟨0, hl, C_zero s _ _⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := (lt_indexedSup_iff length g x).mp hx
    exact ⟨i, hi, C_seed s _ _ x hxi⟩
  · intro x y hx hy
    obtain ⟨i, hi, hix, hiy⟩ := combine x y hx hy
    exact ⟨i, hi, C_add s _ _ x y hix hiy⟩
  · intro x y hx hy
    obtain ⟨i, hi, hix, hiy⟩ := combine x y hx hy
    exact ⟨i, hi, C_index s _ _ x y hix hiy⟩
  · intro k b hb hk hx hy
    obtain ⟨i, hi, hik, hib⟩ := combine k b hx hy
    obtain ⟨j, hj, hbj⟩ := (lt_indexedSup_iff length f b).mp hb
    rcases lt_total i j with hij | hij | hji
    · exact ⟨j, hj, C_collapse s _ _ k b hbj hk
        (promote i j (Or.inl hij) hj k hik) (promote i j (Or.inl hij) hj b hib)⟩
    · exact ⟨j, hj, C_collapse s _ _ k b hbj hk (hij ▸ hik) (hij ▸ hib)⟩
    · exact ⟨i, hi, C_collapse s _ _ k b
        (lt_of_lt_of_le hbj (hf j i (Or.inl hji) hi)) hk hik hib⟩

theorem psi_indexedSup (s : Supply) (k length : O) (hl : 0 < length) (f : O → O)
    (hf : ∀ i j, i ≤ j → j < length → f i ≤ f j) :
    psi s k (indexedSup length f) = indexedSup length (fun i => psi s k (f i)) := by
  let g := fun i => psi s k (f i)
  have hg : ∀ i j, i ≤ j → j < length → g i ≤ g j :=
    fun i j hij hj => psi_mono s k _ _ (hf i j hij hj)
  apply le_antisymm
  · apply psi_min
    refine ⟨indexedSup_le length g k (fun i _ => psi_le s k (f i)), ?_⟩
    intro x hx hxk
    obtain ⟨i, hi, hix⟩ := C_directed_indexedSup s length hl f g hf hg x hx
    exact lt_of_lt_of_le (psi_closed s k (f i) x hix hxk) (le_indexedSup _ _ hi)
  · exact indexedSup_le length g _ (fun i hi => psi_mono s k _ _ (le_indexedSup _ _ hi))

theorem psi_transfiniteFundamentalSequence (s : Supply) (k a length : O) (f : O → O)
    (hk : RegularIndex s k) (hl : 0 < length)
    (hf : TransfiniteFundamentalSequence a length f)
    (hindex : ∀ i, i < length → C s (f i) (psi s k (f i)) k)
    (harg : ∀ i, i < length → C s (f i) (psi s k (f i)) (f i)) :
    TransfiniteFundamentalSequence (psi s k a) length (fun i => psi s k (f i)) := by
  have hm : ∀ i j, i ≤ j → j < length → f i ≤ f j := fun _ _ => hf.mono
  have heq : psi s k a = indexedSup length (fun i => psi s k (f i)) := by
    rw [← hf.sup_eq]
    exact psi_indexedSup s k length hl f hm
  refine ⟨fun i hi => psi_strict_of_mem s k _ _ hk (hf.below i hi)
      (hindex i hi) (harg i hi),
    fun i j hij hj => psi_strict_of_mem s k _ _ hk (hf.strict i j hij hj)
      (hindex i (lt_trans _ _ _ hij hj)) (harg i (lt_trans _ _ _ hij hj)), ?_⟩
  intro x hx
  exact (lt_indexedSup_iff _ _ _).mp (heq ▸ hx)

end
end OCF.Denis
