import Multi.term3.Denis.Sequences

/-! Rank and index laws for I. These prove the comparisons and closure
properties used by the general inaccessible-collapse sequence rules. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem inaccessible_down {r q k : O} (hrq : r ≤ q) (hk : Inaccessible q k) :
    Inaccessible r k := by
  rw [inaccessible_iff] at hk ⊢
  exact ⟨hk.1, fun t ht x hx => hk.2 t (lt_of_lt_of_le ht hrq) x hx⟩

theorem next_le (s : Supply) (r lower k : O) (hl : lower < k) (hk : Inaccessible r k) :
    next s r lower ≤ k := least_le _ _ ⟨hl, hk⟩

theorem first_rank_strict (s : Supply) {r q : O} (hrq : r < q) :
    first s r < first s q := by
  have hq := (inaccessible_iff q (first s q)).mp (first_spec s q)
  obtain ⟨y, _, hy, hry⟩ := hq.2 r hrq 0 (regular_pos hq.1)
  exact lt_of_le_of_lt (first_le s r y hry) hy

theorem rank_le_first (s : Supply) (r : O) : r ≤ first s r := by
  induction r using lt_wellFounded.induction with
  | h r ih =>
    apply (not_lt_iff_le _ _).mp
    intro hr
    exact lt_irrefl _ (lt_of_le_of_lt (ih _ hr) (first_rank_strict s hr))

theorem index_le_I (s : Supply) (r b : O) : b ≤ I s r b := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    apply (not_lt_iff_le _ _).mp
    intro hb
    exact lt_irrefl _ (lt_of_le_of_lt (ih _ hb) (I_strict s r hb))

theorem rank_le_I (s : Supply) (r b : O) : r ≤ I s r b := by
  have h := I_mono s r (zero_le b)
  rw [I_zero] at h
  exact le_trans (rank_le_first s r) h

theorem I_addPrincipal (s : Supply) (r b : O) : AddPrincipal (I s r b) := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    classical
    by_cases hz : b = 0
    · subst b
      exact fun _ _ hx hy => regular_add_closed
        (regularIndex_regular s _ (Or.inl ⟨r, rfl⟩)) hx hy
    by_cases hs : ∃ c, b = succ c
    · obtain ⟨c, rfl⟩ := hs
      exact fun _ _ hx hy => regular_add_closed
        (regularIndex_regular s _ (Or.inr ⟨r, c, rfl⟩)) hx hy
    · intro x y hx hy
      rw [I_limit s r b hz hs, lt_sup_iff] at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨j, hj⟩ := hy
      let u := type ((representative b).below i)
      let v := type ((representative b).below j)
      have bound (w : O) (hw : w < b) (hx : x < I s r w) (hy : y < I s r w) :
          x + y < I s r b :=
        lt_trans _ _ _ (ih w hw x y hx hy) (I_strict s r hw)
      rcases lt_total u v with h | h | h
      · exact bound v (initial_lt b j) (lt_trans _ _ _ hi (I_strict s r h)) hj
      · exact bound v (initial_lt b j) (h ▸ hi) hj
      · exact bound u (initial_lt b i) hi (lt_trans _ _ _ hj (I_strict s r h))

theorem I_lt_inaccessible (s : Supply) {q k : O} (hk : Inaccessible q k)
    (r b : O) (hr : r < q) (hb : b < k) : I s r b < k := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    classical
    have hreg := inaccessible_regular hk
    have hlimit := ((inaccessible_iff q k).mp hk).2 r hr
    by_cases hz : b = 0
    · subst b
      rw [I_zero]
      obtain ⟨y, _, hy, hry⟩ := hlimit 0 (regular_pos hreg)
      exact lt_of_le_of_lt (first_le s r y hry) hy
    by_cases hs : ∃ c, b = succ c
    · obtain ⟨c, rfl⟩ := hs
      have hc := ih c (lt_succ_self c) (lt_trans _ _ _ (lt_succ_self c) hb)
      obtain ⟨y, hy, hyk, hry⟩ := hlimit (I s r c) hc
      rw [I_succ]
      exact lt_of_le_of_lt (next_le s r _ y hy hry) hyk
    · rw [I_limit s r b hz hs]
      obtain ⟨bound, hbound, hfb⟩ := hreg.2 b hb
        (fun i => I s r (type ((representative b).below i)))
        (fun i => ih _ (initial_lt b i) (lt_trans _ _ _ (initial_lt b i) hb))
      exact lt_of_le_of_lt ((sup_le_iff _ bound).mpr (fun i => Or.inl (hfb i))) hbound

/-- Every higher-rank index is closed under lower-rank enumeration. -/
theorem I_lower_rank_closed (s : Supply) (r q b x : O) (hrq : r < q)
    (hx : x < I s q b) : I s r x < I s q b := by
  classical
  by_cases hz : b = 0
  · subst b
    have hk : Inaccessible q (I s q 0) := by rw [I_zero]; exact first_spec s q
    exact I_lt_inaccessible s hk r x hrq hx
  by_cases hs : ∃ c, b = succ c
  · obtain ⟨c, rfl⟩ := hs
    have hk : Inaccessible q (I s q (succ c)) := by rw [I_succ]; exact (next_spec s q _).2
    exact I_lt_inaccessible s hk r x hrq hx
  · have h := hx
    rw [I_limit s q b hz hs, lt_sup_iff] at h
    obtain ⟨i, hi⟩ := h
    let c := type ((representative b).below i)
    have hcb := succ_lt_limit ⟨hz, hs⟩ (initial_lt b i)
    have hk : Inaccessible q (I s q (succ c)) := by rw [I_succ]; exact (next_spec s q _).2
    exact lt_trans _ _ _
      (I_lt_inaccessible s hk r x hrq (lt_trans _ _ _ hi (I_strict s q (lt_succ_self c))))
      (I_strict s q hcb)

/-- Normal I expressions have unique rank and index. -/
theorem I_normal_injective (s : Supply) (r b q c : O)
    (hb : b < I s r b) (hc : c < I s q c) (heq : I s r b = I s q c) :
    r = q ∧ b = c := by
  have hr : r = q := by
    rcases lt_total r q with h | h | h
    · have hh := I_lower_rank_closed s r q c b h (heq ▸ hb)
      rw [heq] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact h
    · have hh := I_lower_rank_closed s q r b c h (heq.symm ▸ hc)
      rw [heq] at hh
      exact False.elim (lt_irrefl _ hh)
  subst q
  refine ⟨rfl, ?_⟩
  rcases lt_total b c with h | h | h
  · have hh := I_strict s r h
    rw [heq] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := I_strict s r h
    rw [heq] at hh
    exact False.elim (lt_irrefl _ hh)

/-- A normal I expression cannot denote a collapse value. -/
theorem I_normal_ne_psi (s : Supply) (r b k a : O) (hk : UncountableRegular k)
    (hr : r < I s r b) (hb : b < I s r b) : I s r b ≠ psi s k a := by
  intro heq
  rw [heq] at hr hb
  have hc := C_index s a (psi s k a) r b (C_seed s a _ r hr) (C_seed s a _ b hb)
  rw [heq] at hc
  exact lt_irrefl _ (psi_closed s k a _ hc (psi_lt s k a hk))

end
end OCF.Denis
