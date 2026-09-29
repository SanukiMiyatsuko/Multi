import Multi.term3.Denis.RegularDiagonals

/-! Diagonal collapse with an arbitrary admissible starting argument.
The index only has to be in the starting closure, rather than in every
closure at every positive cutoff. -/

namespace OCF.Denis
open Ordinal
noncomputable section

structure DiagonalSeed (s : Supply) (r c : O) : Prop where
  below : c < r
  argument : C s c (psi s (I s 0 0) c) c
  index : C s c (psi s (I s 0 0) c) r

theorem DiagonalSeed.growth {s : Supply} {r c : O}
    (hc : DiagonalSeed s r c) (hlarge : I s 0 0 < r) : c < psi s r c := by
  have hb := lt_trans _ _ _ (psi_lt s _ c (first_regular s)) (first_lt_psi_above s r c hlarge)
  exact psi_closed s r c c (C_mono_seed s c _ _ (Or.inl hb) c hc.argument) hc.below

theorem DiagonalSeed.step {s : Supply} {r c : O} (hc : DiagonalSeed s r c)
    (hr : RegularIndex s r) (hlarge : I s 0 0 < r) : DiagonalSeed s r (psi s r c) := by
  have h := hc.growth hlarge
  have promote (x : O) (hx : C s c (psi s (I s 0 0) c) x) :
      C s (psi s r c) (psi s (I s 0 0) (psi s r c)) x :=
    C_mono_seed s _ _ _ (psi_mono s _ _ _ (Or.inl h)) x
      (C_mono_argument s _ _ _ (Or.inl h) x hx)
  exact ⟨psi_lt s r c (regularIndex_regular s r hr),
    C_collapse s _ _ r c h hr (promote r hc.index) (promote c hc.argument), promote r hc.index⟩

def seededIter (s : Supply) (r c : O) : Nat → O
  | 0 => c
  | n + 1 => psi s r (seededIter s r c n)

theorem seededIter_seed (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) (n : Nat) :
    DiagonalSeed s r (seededIter s r c n) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact ih.step hr hlarge

theorem seededIter_lt_succ (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) (n : Nat) :
    seededIter s r c n < seededIter s r c (n + 1) :=
  (seededIter_seed s r c hr hlarge hc n).growth hlarge

theorem seededIter_strict (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) {n m : Nat} (h : n < m) :
    seededIter s r c n < seededIter s r c m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hl | rfl
    · exact lt_trans _ _ _ (ih hl) (seededIter_lt_succ s r c hr hlarge hc m)
    · exact seededIter_lt_succ s r c hr hlarge hc n

theorem seededIter_mono (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) {n m : Nat} (h : n ≤ m) :
    seededIter s r c n ≤ seededIter s r c m := by
  rcases Nat.lt_or_eq_of_le h with hl | rfl
  · exact Or.inl (seededIter_strict s r c hr hlarge hc hl)
  · exact le_refl _

def seededSeq (s : Supply) (r c : O) (n : Nat) : O :=
  psi s (I s 0 0) (seededIter s r c n)

theorem seededSeq_mono (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) {n m : Nat} (h : n ≤ m) :
    seededSeq s r c n ≤ seededSeq s r c m :=
  psi_mono s _ _ _ (seededIter_mono s r c hr hlarge hc h)

theorem seededSeq_lt_next (s : Supply) (r c : O) (hlarge : I s 0 0 < r) (n : Nat) :
    seededSeq s r c n < seededIter s r c (n + 1) :=
  lt_trans _ _ _ (psi_lt s _ _ (first_regular s)) (first_lt_psi_above s r _ hlarge)

theorem C_seeded_sup (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c)
    (x : O) (hx : C s r (sup (seededSeq s r c)) x) :
    ∃ n, C s (seededIter s r c n) (seededSeq s r c n) x := by
  let f := seededIter s r c
  let g := seededSeq s r c
  have promote (n m : Nat) (hnm : n ≤ m) (x : O) (hx : C s (f n) (g n) x) :
      C s (f m) (g m) x :=
    C_mono_seed s _ _ _ (seededSeq_mono s r c hr hlarge hc hnm) x
      (C_mono_argument s _ _ _ (seededIter_mono s r c hr hlarge hc hnm) x hx)
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
  · intro k b hb hk hx hy
    obtain ⟨n, hn, hm⟩ := combine k b hx hy
    have hb' : b < f (n + 1) := psi_closed s r (f n) b
      (C_mono_seed s _ _ _ (Or.inl (seededSeq_lt_next s r c hlarge n)) b hm) hb
    exact ⟨n + 1, C_collapse s _ _ k b hb' hk
      (promote n _ (Nat.le_succ n) k hn) (promote n _ (Nat.le_succ n) b hm)⟩

theorem seededSeq_sup (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) :
    sup (seededSeq s r c) = psi s (I s 0 0) r := by
  apply le_antisymm
  · exact (sup_le_iff _ _).mpr (fun n => psi_mono s _ _ _
      (Or.inl (seededIter_seed s r c hr hlarge hc n).below))
  · apply psi_min
    refine ⟨(sup_le_iff _ _).mpr (fun n => psi_le s _ _), ?_⟩
    intro x hx hxk
    obtain ⟨n, hn⟩ := C_seeded_sup s r c hr hlarge hc x hx
    exact lt_of_lt_of_le (psi_closed s _ _ x hn hxk) (le_sup (seededSeq s r c) n)

theorem seeded_fundamentalSequence (s : Supply) (r c : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hc : DiagonalSeed s r c) :
    FundamentalSequence (psi s (I s 0 0) r) (seededSeq s r c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact psi_strict_of_mem s _ _ _ (Or.inl ⟨0, rfl⟩)
      (seededIter_seed s r c hr hlarge hc n).below (first_mem_C s _ _)
      (seededIter_seed s r c hr hlarge hc n).argument
  · intro n m h
    exact psi_strict_of_mem s _ _ _ (Or.inl ⟨0, rfl⟩)
      (seededIter_strict s r c hr hlarge hc h) (first_mem_C s _ _)
      (seededIter_seed s r c hr hlarge hc n).argument
  · intro x hx
    rw [← seededSeq_sup s r c hr hlarge hc, lt_sup_iff] at hx
    exact hx

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem seededIter_represented (s : OCF.Denis.Supply) (r c : OCF.Denis.O)
    (hr : Represented s r) (hc : Represented s c) (hreg : OCF.Denis.RegularIndex s r)
    (hlarge : OCF.Denis.I s 0 0 < r) (hseed : OCF.Denis.DiagonalSeed s r c) (n : Nat) :
    Represented s (OCF.Denis.seededIter s r c n) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact represented_psi_of_mem s r _ hr ih hreg
      (OCF.Denis.C_seed s _ _ _ (OCF.Denis.seededIter_lt_succ s r c hreg hlarge hseed n))

theorem seeded_diagonal_dense (s : OCF.Denis.Supply) (r c : OCF.Denis.O)
    (hr : Represented s r) (hc : Represented s c) (hreg : OCF.Denis.RegularIndex s r)
    (hlarge : OCF.Denis.I s 0 0 < r) (hseed : OCF.Denis.DiagonalSeed s r c) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) r) := by
  apply dense_of_normal_sequence s _ _ (OCF.Denis.seeded_fundamentalSequence s r c hreg hlarge hseed)
  intro n
  exact represented_psi_of_mem s _ _ ⟨omega1, omega1_isNormal s, rfl⟩
    (seededIter_represented s r c hr hc hreg hlarge hseed n) (Or.inl ⟨0, rfl⟩)
    (OCF.Denis.seededIter_seed s r c hreg hlarge hseed n).argument

end
end T.Correspondence.Denis.Covering
