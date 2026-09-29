import Multi.term3.Denis.Collapse
import Multi.term3.Denis.Small

/-! Strict existence of Denis's collapsing function on actual ordinals.
The proof bounds finite closure expressions, iterates the bound countably
many times, and uses regularity to stay strictly below the index.
-/

namespace OCF.Denis

open Ordinal

noncomputable section

def evaluate (s : Supply) (a beta : O) : Expr (representative beta).Carrier → O
  | .zero => 0
  | .leaf x => type ((representative beta).below x)
  | .node op x y =>
    if op = 0 then evaluate s a beta x + evaluate s a beta y
    else if op = 1 then I s (evaluate s a beta x) (evaluate s a beta y)
    else psi s (evaluate s a beta x) (evaluate s a beta y)

theorem C_has_code (s : Supply) (a beta x : O) (hx : C s a beta x) :
    ∃ c, evaluate s a beta c = x := by
  apply C_least s a beta (fun x => ∃ c, evaluate s a beta c = x) _ _ _ _ _ x hx
  · exact ⟨.zero, rfl⟩
  · intro x hx
    obtain ⟨y, hy⟩ := initial_surjective beta x hx
    exact ⟨.leaf y, hy.symm⟩
  · rintro x y ⟨cx, hx⟩ ⟨cy, hy⟩
    exact ⟨.node 0 cx cy, by simp only [evaluate, ↓reduceIte, hx, hy]⟩
  · rintro x y ⟨cx, hx⟩ ⟨cy, hy⟩
    exact ⟨.node 1 cx cy, by simp [evaluate, hx, hy]⟩
  · rintro k b hb hk ⟨ck, hck⟩ ⟨cb, hcb⟩
    exact ⟨.node 2 ck cb, by simp [evaluate, hck, hcb]⟩

theorem C_bounded (s : Supply) (a k beta : O) (hk : UncountableRegular k) (hb : beta < k) :
    ∃ bound, bound < k ∧ ∀ x, C s a beta x → x < k → x < bound := by
  classical
  let f : Expr (representative beta).Carrier → O :=
    fun c => if evaluate s a beta c < k then evaluate s a beta c else 0
  have hf : ∀ c, f c < k := by
    intro c
    dsimp [f]
    split
    · assumption
    · exact regular_pos hk
  obtain ⟨bound, hbound, hfb⟩ :=
    small_expr hk (small_representative hk beta hb) f hf
  refine ⟨bound, hbound, ?_⟩
  intro x hx hxk
  obtain ⟨c, hc⟩ := C_has_code s a beta x hx
  have h := hfb c
  dsimp [f] at h
  rw [hc, ite_eq_left hxk] at h
  exact h

def nextBound (s : Supply) (a k : O) (hk : UncountableRegular k)
    (beta : {b : O // b < k}) : {b : O // b < k} :=
  ⟨Classical.choose (C_bounded s a k beta.1 hk beta.2),
    (Classical.choose_spec (C_bounded s a k beta.1 hk beta.2)).1⟩

theorem nextBound_spec (s : Supply) (a k : O) (hk : UncountableRegular k)
    (beta : {b : O // b < k}) (x : O) (hx : C s a beta.1 x) (hxk : x < k) :
    x < (nextBound s a k hk beta).1 :=
  (Classical.choose_spec (C_bounded s a k beta.1 hk beta.2)).2 x hx hxk

theorem le_nextBound (s : Supply) (a k : O) (hk : UncountableRegular k)
    (beta : {b : O // b < k}) : beta.1 ≤ (nextBound s a k hk beta).1 := by
  apply (not_lt_iff_le _ _).mp
  intro h
  exact lt_irrefl _ (nextBound_spec s a k hk beta _
    (C_seed s a beta.1 _ h) (nextBound s a k hk beta).2)

def bounds (s : Supply) (a k : O) (hk : UncountableRegular k) : Nat → {b : O // b < k}
  | 0 => ⟨0, regular_pos hk⟩
  | n + 1 => nextBound s a k hk (bounds s a k hk n)

theorem bounds_mono (s : Supply) (a k : O) (hk : UncountableRegular k)
    (n m : Nat) (hnm : n ≤ m) : (bounds s a k hk n).1 ≤ (bounds s a k hk m).1 := by
  induction hnm with
  | refl => exact le_refl _
  | @step m hnm ih => exact le_trans ih (le_nextBound s a k hk (bounds s a k hk m))

def closureBound (s : Supply) (a k : O) (hk : UncountableRegular k) : O :=
  sup (fun n => (bounds s a k hk n).1)

theorem closureBound_lt (s : Supply) (a k : O) (hk : UncountableRegular k) :
    closureBound s a k hk < k := by
  obtain ⟨b, hb, hbound⟩ := small_nat hk (fun n => (bounds s a k hk n).1)
    (fun n => (bounds s a k hk n).2)
  exact lt_of_le_of_lt ((sup_le_iff _ b).mpr (fun n => Or.inl (hbound n))) hb

theorem C_closureBound_finite (s : Supply) (a k : O) (hk : UncountableRegular k)
    (x : O) (hx : C s a (closureBound s a k hk) x) :
    ∃ n, C s a (bounds s a k hk n).1 x := by
  have combine (x y : O) (hx : ∃ n, C s a (bounds s a k hk n).1 x)
      (hy : ∃ n, C s a (bounds s a k hk n).1 y) :
      ∃ n, C s a (bounds s a k hk n).1 x ∧ C s a (bounds s a k hk n).1 y := by
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m,
      C_mono_seed s a _ _ (bounds_mono s a k hk n _ (Nat.le_max_left _ _)) x hn,
      C_mono_seed s a _ _ (bounds_mono s a k hk m _ (Nat.le_max_right _ _)) y hm⟩
  apply C_least s a (closureBound s a k hk)
    (fun x => ∃ n, C s a (bounds s a k hk n).1 x) _ _ _ _ _ x hx
  · exact ⟨0, C_zero s a _⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (lt_sup_iff _ x).mp hx
    exact ⟨n, C_seed s a _ x hn⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_add s a _ x y hn hm⟩
  · intro x y hx hy
    obtain ⟨n, hn, hm⟩ := combine x y hx hy
    exact ⟨n, C_index s a _ x y hn hm⟩
  · intro j b hb hj hx hy
    obtain ⟨n, hn, hm⟩ := combine j b hx hy
    exact ⟨n, C_collapse s a _ j b hb hj hn hm⟩

theorem closureBound_closed (s : Supply) (a k : O) (hk : UncountableRegular k)
    (x : O) (hx : C s a (closureBound s a k hk) x) (hxk : x < k) :
    x < closureBound s a k hk := by
  obtain ⟨n, hn⟩ := C_closureBound_finite s a k hk x hx
  have h := nextBound_spec s a k hk (bounds s a k hk n) x hn hxk
  exact lt_of_lt_of_le h (le_sup (fun n => (bounds s a k hk n).1) (n + 1))

/-- Existence of a strict closure point, proved from ordinary regularity. -/
theorem strict_closure_exists (s : Supply) (k a : O) (hk : UncountableRegular k) :
    ∃ beta, beta < k ∧ ∀ x, C s a beta x → x < k → x < beta :=
  ⟨closureBound s a k hk, closureBound_lt s a k hk, closureBound_closed s a k hk⟩

theorem psi_lt (s : Supply) (k a : O) (hk : UncountableRegular k) : psi s k a < k :=
  (psi_lt_iff s k a).mpr (strict_closure_exists s k a hk)

/-- The exact minimum required in the source, at every allowed index. -/
theorem psi_spec (s : Supply) (k a : O) (hk : RegularIndex s k) :
    psi s k a < k ∧
    (∀ x, C s a (psi s k a) x → x < k → x < psi s k a) ∧
    (∀ beta, beta < k →
      (∀ x, C s a beta x → x < k → x < beta) → psi s k a ≤ beta) :=
  ⟨psi_lt s k a (regularIndex_regular s k hk), psi_closed s k a,
    fun beta hb hc => psi_min s k a beta ⟨Or.inl hb, hc⟩⟩

/-- Existence and uniqueness of the ordinal in the original minimum definition. -/
theorem psi_exists_unique (s : Supply) (k a : O) (hk : RegularIndex s k) :
    ∃ beta, (beta < k ∧
      (∀ x, C s a beta x → x < k → x < beta) ∧
      (∀ gamma, gamma < k →
        (∀ x, C s a gamma x → x < k → x < gamma) → beta ≤ gamma)) ∧
      ∀ gamma, (gamma < k ∧
        (∀ x, C s a gamma x → x < k → x < gamma) ∧
        (∀ delta, delta < k →
          (∀ x, C s a delta x → x < k → x < delta) → gamma ≤ delta)) →
        gamma = beta := by
  refine ⟨psi s k a, psi_spec s k a hk, ?_⟩
  intro gamma h
  exact (psi_eq_of_spec s k a gamma h.1 h.2.1 h.2.2).symm

end
end OCF.Denis
