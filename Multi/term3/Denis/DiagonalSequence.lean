import Multi.term3.Denis.EpsilonSequence

/-! The diagonal fundamental-sequence rule at a regular cardinal above
I(0,0), including the first weakly inaccessible cardinal. -/

namespace OCF.Denis
open Ordinal
noncomputable section

def diagonalIter (s : Supply) (r : O) : Nat → O
  | 0 => succ 0
  | n + 1 => psi s r (diagonalIter s r n)

theorem diagonalIter_pos (s : Supply) (r : O) (hr : RegularIndex s r) (n : Nat) :
    0 < diagonalIter s r n := by
  cases n with
  | zero => exact lt_succ_self _
  | succ n => exact psi_pos s r _ (regular_pos (regularIndex_regular s r hr))

theorem diagonalIter_lt (s : Supply) (r : O) (hr : RegularIndex s r) (n : Nat) :
    diagonalIter s r n < r := by
  cases n with
  | zero => exact lt_trans _ _ _ (finite_lt_omega 1) (regularIndex_regular s r hr).1
  | succ n => exact psi_lt s r _ (regularIndex_regular s r hr)

theorem first_lt_psi_above (s : Supply) (r a : O) (hr : I s 0 0 < r) :
    I s 0 0 < psi s r a := psi_closed s r a _ (first_mem_C s _ _) hr

theorem diagonalIter_lt_succ (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r) (n : Nat) :
    diagonalIter s r n < diagonalIter s r (n + 1) := by
  induction n with
  | zero =>
    exact lt_trans _ _ _
      (lt_trans _ _ _ (finite_lt_omega 1) (first_regular s).1)
      (first_lt_psi_above s r _ hlarge)
  | succ n ih =>
    exact psi_strict_of_mem s r _ _ hr ih
      (hindex _ _ (diagonalIter_pos s r hr n)) (C_seed s _ _ _ ih)

theorem diagonalIter_strict (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r)
    {n m : Nat} (h : n < m) : diagonalIter s r n < diagonalIter s r m := by
  induction m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hl | rfl
    · exact lt_trans _ _ _ (ih hl) (diagonalIter_lt_succ s r hr hlarge hindex m)
    · exact diagonalIter_lt_succ s r hr hlarge hindex n

theorem diagonalIter_mono (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r)
    {n m : Nat} (h : n ≤ m) : diagonalIter s r n ≤ diagonalIter s r m := by
  rcases Nat.lt_or_eq_of_le h with hl | rfl
  · exact Or.inl (diagonalIter_strict s r hr hlarge hindex hl)
  · exact le_refl _

theorem diagonalIter_argument_normal (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r) (n : Nat) :
    C s (diagonalIter s r n) (psi s (I s 0 0) (diagonalIter s r n))
      (diagonalIter s r n) := by
  induction n with
  | zero =>
    change C s (succ 0) (psi s (I s 0 0) (succ 0)) (succ 0)
    rw [psi_first_one]
    exact C_seed s _ _ _ (finite_lt_omega 1)
  | succ n ih =>
    have hlt := diagonalIter_lt_succ s r hr hlarge hindex n
    exact C_collapse s _ _ r (diagonalIter s r n) hlt hr
      (hindex _ _ (diagonalIter_pos s r hr (n + 1)))
      (C_mono_seed s _ _ _ (psi_mono s _ _ _ (Or.inl hlt)) _
        (C_mono_argument s _ _ _ (Or.inl hlt) _ ih))

def diagonalSeq (s : Supply) (r : O) (n : Nat) : O :=
  psi s (I s 0 0) (diagonalIter s r n)

theorem diagonalSeq_mono (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r)
    {n m : Nat} (h : n ≤ m) : diagonalSeq s r n ≤ diagonalSeq s r m :=
  psi_mono s _ _ _ (diagonalIter_mono s r hr hlarge hindex h)

theorem diagonalSeq_lt_next (s : Supply) (r : O) (hlarge : I s 0 0 < r) (n : Nat) :
    diagonalSeq s r n < diagonalIter s r (n + 1) :=
  lt_trans _ _ _ (psi_lt s _ _ (first_regular s)) (first_lt_psi_above s r _ hlarge)

/-- A finite expression in the full closure occurs at a finite diagonal stage.
The bound on an earlier collapse argument comes from the inner collapse. -/
theorem C_diagonal_sup (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r)
    (x : O) (hx : C s r (sup (diagonalSeq s r)) x) :
    ∃ n, C s (diagonalIter s r n) (diagonalSeq s r n) x := by
  let f := diagonalIter s r
  let g := diagonalSeq s r
  have promote (n m : Nat) (hnm : n ≤ m) (x : O) (hx : C s (f n) (g n) x) :
      C s (f m) (g m) x :=
    C_mono_seed s _ _ _ (diagonalSeq_mono s r hr hlarge hindex hnm) x
      (C_mono_argument s _ _ _ (diagonalIter_mono s r hr hlarge hindex hnm) x hx)
  have combine (x y : O) (hx : ∃ n, C s (f n) (g n) x)
      (hy : ∃ n, C s (f n) (g n) y) :
      ∃ n, C s (f n) (g n) x ∧ C s (f n) (g n) y := by
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨max n m, promote n _ (Nat.le_max_left _ _) x hn,
      promote m _ (Nat.le_max_right _ _) y hm⟩
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
      (C_mono_seed s _ _ _ (Or.inl (diagonalSeq_lt_next s r hlarge n)) b hm) hb
    exact ⟨n + 1, C_collapse s _ _ k b hb' hk
      (promote n _ (Nat.le_succ n) k hn) (promote n _ (Nat.le_succ n) b hm)⟩

theorem diagonalSeq_sup (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r) :
    sup (diagonalSeq s r) = psi s (I s 0 0) r := by
  apply le_antisymm
  · exact (sup_le_iff _ _).mpr (fun n => psi_mono s _ _ _ (Or.inl (diagonalIter_lt s r hr n)))
  · apply psi_min
    refine ⟨(sup_le_iff _ _).mpr (fun n => psi_le s _ _), ?_⟩
    intro x hx hxk
    obtain ⟨n, hn⟩ := C_diagonal_sup s r hr hlarge hindex x hx
    exact lt_of_lt_of_le (psi_closed s _ _ x hn hxk) (le_sup (diagonalSeq s r) n)

theorem diagonal_fundamentalSequence (s : Supply) (r : O) (hr : RegularIndex s r)
    (hlarge : I s 0 0 < r) (hindex : ∀ a b, 0 < a → C s a b r) :
    FundamentalSequence (psi s (I s 0 0) r) (diagonalSeq s r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact psi_strict_of_mem s _ _ _ (Or.inl ⟨0, rfl⟩) (diagonalIter_lt s r hr n)
      (first_mem_C s _ _) (diagonalIter_argument_normal s r hr hlarge hindex n)
  · intro n m h
    exact psi_strict_of_mem s _ _ _ (Or.inl ⟨0, rfl⟩)
      (diagonalIter_strict s r hr hlarge hindex h)
      (first_mem_C s _ _) (diagonalIter_argument_normal s r hr hlarge hindex n)
  · intro x hx
    rw [← diagonalSeq_sup s r hr hlarge hindex, lt_sup_iff] at hx
    exact hx

theorem first_lt_first_inaccessible (s : Supply) : I s 0 0 < I s (succ 0) 0 := by
  have h : Inaccessible (succ 0) (I s (succ 0) 0) := by
    rw [I_zero]
    exact first_spec s _
  have hreg := inaccessible_regular h
  obtain ⟨y, _, hy, hyreg⟩ := (inaccessible_iff _ _).mp h |>.2
    0 (lt_succ_self 0) 0 (regular_pos hreg)
  rw [I_zero s 0]
  exact lt_of_le_of_lt (first_le s 0 y hyreg) hy

theorem first_inaccessible_mem_C (s : Supply) (a b : O) (ha : 0 < a) :
    C s a b (I s (succ 0) 0) := by
  have hone := C_collapse s a b (I s 0 0) 0 ha (Or.inl ⟨0, rfl⟩)
    (first_mem_C s a b) (C_zero s a b)
  rw [psi_first_zero] at hone
  exact C_index s a b _ _ hone (C_zero s a b)

theorem inaccessible_diagonal_fundamentalSequence (s : Supply) :
    FundamentalSequence (psi s (I s 0 0) (I s (succ 0) 0))
      (diagonalSeq s (I s (succ 0) 0)) :=
  diagonal_fundamentalSequence s _ (Or.inl ⟨succ 0, rfl⟩)
    (first_lt_first_inaccessible s) (first_inaccessible_mem_C s)

end
end OCF.Denis
