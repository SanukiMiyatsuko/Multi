import Multi.term3.Denis.NormalClosureStage

/-! Ordinals denoted by normal terms are exactly the elements of the
closures `C(A, 0)`.

A derivation in the Jäger-style closure uses only proper collapses, so it
can be read as a normal term. Completeness of that closure then shows that
every element of `C(A, 0)` is denoted by a normal term. In particular
represented ordinals are closed under every collapse at a regular index,
with no argument condition. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem represented_of_PC_zero (s : OCF.Denis.Supply) (A x : OCF.Denis.O)
    (hx : OCF.Denis.PC s A 0 x) : Represented s x := by
  induction hx with
  | zero => exact represented_zero s
  | seed hx => exact False.elim (not_lt_zero _ hx)
  | add _ _ ihx ihy => exact represented_add s _ _ ihx ihy
  | index _ _ ihx ihy => exact represented_I s _ _ ihx ihy
  | collapse _ hp _ _ ihk ihb => exact represented_psi_of_mem s _ _ ihk ihb hp.1 hp.2.2

theorem represented_of_C_zero (s : OCF.Denis.Supply) (A x : OCF.Denis.O)
    (hx : OCF.Denis.C s A 0 x) : Represented s x :=
  represented_of_PC_zero s A x (OCF.Denis.properClosureComplete s A 0 x hx)

theorem C_zero_pair (s : OCF.Denis.Supply) (x y : OCF.Denis.O)
    (hx : ∃ A, OCF.Denis.C s A 0 x) (hy : ∃ A, OCF.Denis.C s A 0 y) :
    ∃ A, OCF.Denis.C s A 0 x ∧ OCF.Denis.C s A 0 y := by
  obtain ⟨A1, h1⟩ := hx
  obtain ⟨A2, h2⟩ := hy
  rcases OCF.Ordinal.lt_total A1 A2 with h | rfl | h
  · exact ⟨A2, OCF.Denis.C_mono_argument s A1 A2 0 (Or.inl h) x h1, h2⟩
  · exact ⟨A1, h1, h2⟩
  · exact ⟨A1, h1, OCF.Denis.C_mono_argument s A2 A1 0 (Or.inl h) y h2⟩

theorem C_zero_of_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) :
    ∃ A, OCF.Denis.C s A 0 (denote s t) := by
  induction ht with
  | zero => exact ⟨0, OCF.Denis.C_zero s 0 0⟩
  | @index r b _ _ _ _ ihr ihb =>
    obtain ⟨A, hr, hb⟩ := C_zero_pair s _ _ ihr ihb
    exact ⟨A, OCF.Denis.C_index s A 0 _ _ hr hb⟩
  | @collapse k a _ _ hreg _ ihk iha =>
    obtain ⟨A, hk, ha⟩ := C_zero_pair s _ _ ihk iha
    have hex : ∃ B, denote s a < B ∧ OCF.Denis.C s B 0 (denote s k) ∧
        OCF.Denis.C s B 0 (denote s a) := by
      rcases OCF.Ordinal.lt_total (denote s a) A with h | h | h
      · exact ⟨A, h, hk, ha⟩
      · refine ⟨succ A, by rw [h]; exact lt_succ_self A, ?_, ?_⟩
        · exact OCF.Denis.C_mono_argument s A _ 0 (Or.inl (lt_succ_self A)) _ hk
        · exact OCF.Denis.C_mono_argument s A _ 0 (Or.inl (lt_succ_self A)) _ ha
      · have hAs : A ≤ succ (denote s a) := Or.inl (OCF.Ordinal.lt_trans _ _ _ h (lt_succ_self _))
        exact ⟨succ (denote s a), lt_succ_self _, OCF.Denis.C_mono_argument s A _ 0 hAs _ hk,
          OCF.Denis.C_mono_argument s A _ 0 hAs _ ha⟩
    obtain ⟨B, hB, hkB, haB⟩ := hex
    exact ⟨B, OCF.Denis.C_collapse s B 0 _ _ hB hreg hkB haB⟩
  | @sum u v _ _ _ _ _ _ ihu ihv =>
    obtain ⟨A, hu, hv⟩ := C_zero_pair s _ _ ihu ihv
    exact ⟨A, OCF.Denis.C_add s A 0 _ _ hu hv⟩

theorem represented_iff_C_zero (s : OCF.Denis.Supply) (x : OCF.Denis.O) :
    Represented s x ↔ ∃ A, OCF.Denis.C s A 0 x := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact C_zero_of_normal s t ht
  · rintro ⟨A, hA⟩
    exact represented_of_C_zero s A x hA

/-- Represented ordinals are closed under every collapse at a regular
index, without any argument condition. -/
theorem represented_psi (s : OCF.Denis.Supply) (k b : OCF.Denis.O)
    (hk : Represented s k) (hb : Represented s b) (hreg : OCF.Denis.RegularIndex s k) :
    Represented s (OCF.Denis.psi s k b) := by
  obtain ⟨A, hkA, hbA⟩ := C_zero_pair s _ _ ((represented_iff_C_zero s k).mp hk)
    ((represented_iff_C_zero s b).mp hb)
  have hAB : A ≤ A + succ b := le_add A (succ b)
  have hbB : b < A + succ b := OCF.Ordinal.lt_of_lt_of_le (lt_succ_self b) (right_le_add A (succ b))
  exact represented_of_C_zero s (A + succ b) _
    (OCF.Denis.C_collapse s _ 0 k b hbB hreg (OCF.Denis.C_mono_argument s A _ 0 hAB k hkA)
      (OCF.Denis.C_mono_argument s A _ 0 hAB b hbA))

end
end T.Correspondence.Denis.Covering
