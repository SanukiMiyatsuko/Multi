import Multi.term3.Denis.IsolatedDiagonal

/-! The barrier lemma.

If `(k, e0)` is proper and an element of `C(A, beta)` lies in the interval
`[psi k e0, psi k (succ e0))`, with the seed at most `psi k e0`, then
`e0` itself belongs to `C(A, beta)`. The index is recovered by the gap
lemma, the next collapse value by the separation invariant of the ceiling
induction, and the argument by general parameter recovery. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem completeBelow_all (s : Supply) (A : O) : CompleteBelow s A :=
  fun a' _ beta x hx => properClosureComplete s a' beta x hx

/-- The barrier at the smallest cutoff above the argument. -/
theorem C_barrier_succ (s : Supply) (beta k e0 x : O) (hbeta : beta ≤ psi s k e0)
    (hx : C s (succ e0) beta x) (hlo : psi s k e0 ≤ x) (hxk : x < k) :
    C s (succ e0) beta e0 := by
  apply Classical.byContradiction
  intro hnot
  have hnot' : ¬ C s e0 beta e0 := fun h =>
    hnot (C_mono_argument s e0 (succ e0) beta (Or.inl (lt_succ_self e0)) e0 h)
  have hx' := C_successor_of_argument_not_mem s e0 beta hnot' x hx
  have hx'' : C s e0 (psi s k e0) x := C_mono_seed s e0 beta _ hbeta x hx'
  exact (not_lt_iff_le _ _).mpr hlo (psi_closed s k e0 x hx'' hxk)

theorem C_barrier (s : Supply) (A beta k e0 x : O)
    (hp : ProperCollapse s k e0) (hbeta : beta ≤ psi s k e0) (he0 : e0 < A)
    (hx : C s A beta x) (hlo : psi s k e0 ≤ x) (hhi : x < psi s k (succ e0)) :
    C s A beta e0 := by
  classical
  have hk := hp.1
  have hreg := regularIndex_regular s k hk
  have hkv : psi s k e0 < k := psi_lt s k e0 hreg
  have hxk : x < k := lt_trans _ _ _ hhi (psi_lt s k _ hreg)
  -- the index belongs to the closure
  obtain ⟨r0, z0, hI, hr0, hz0, hr0C, hz0C⟩ :=
    C_regular_normal_presentation s e0 (psi s k e0) k hreg (Or.inl hkv) hp.2.1
  have hkC : C s A beta k := by
    apply C_index_gap s A beta (psi s k e0) k r0 z0 (psi_addPrincipal s k e0 hreg) hbeta hI
      (psi_closed s k e0 r0 hr0C hr0) (psi_closed s k e0 z0 hz0C hz0) _ x hx hlo hxk
    intro r z hr hz hrz
    exact psi_closed s k e0 _ (C_index s e0 _ r z (C_seed s e0 _ r hr) (C_seed s e0 _ z hz)) hrz
  rcases lt_total (succ e0) A with h1 | h1 | h1
  · rcases lt_total (succ (succ e0)) A with h2 | h2 | h2
    · -- the separation invariant gives the next collapse value
      have hctx : CeilCtx s A beta (succ (succ e0)) (psi s k e0) :=
        { below := completeBelow_all s A
          ca := h2
          bg := hbeta
          c0 := lt_of_le_of_lt (zero_le _) (lt_succ_self _)
          Q := fun d hd k' hk' hk'P hdP =>
            pcCollapseStep_holds s A beta k' d (completeBelow_all s A) hk' hk'P hdP
              (lt_trans _ _ _ hd h2) }
      have he0C : C s (succ (succ e0)) (psi s k e0) e0 :=
        C_mono_argument s e0 _ _ (Or.inl (lt_trans _ _ _ (lt_succ_self e0) (lt_succ_self _))) e0
          hp.2.2
      have hse0C : C s (succ (succ e0)) (psi s k e0) (succ e0) :=
        C_succ s _ _ e0 (lt_of_le_of_lt (zero_le _) (lt_succ_self _)) he0C
      have hkD : C s (succ (succ e0)) (psi s k e0) k :=
        C_mono_argument s e0 _ _ (Or.inl (lt_trans _ _ _ (lt_succ_self e0) (lt_succ_self _))) k
          hp.2.1
      have hsep : IsSep s (succ (succ e0)) (psi s k e0) k x (psi s k (succ e0)) := by
        refine ⟨succ e0, lt_succ_self _, hse0C, rfl, hhi, fun d' hd'c _ hxd' => ?_⟩
        rcases (lt_succ_iff_le _ _).mp hd'c with hlt | heq
        · exact False.elim ((not_lt_iff_le _ _).mpr
            (le_trans (psi_mono s k d' e0 ((lt_succ_iff_le _ _).mp hlt)) hlo) hxd')
        · rw [heq]
          exact le_refl _
      have hxP : PC s A beta x := properClosureComplete s A beta x hx
      have hnext := (hctx.inv_all x hxP 0 x (zero_add x).symm).2 k _ hk hkD
        (properClosureComplete s A beta k hkC) hsep
      have hp' : ProperCollapse s k (succ e0) := by
        refine ⟨hk, ?_, ?_⟩
        · exact C_mono_seed s _ _ _ (psi_mono s k e0 _ (Or.inl (lt_succ_self e0))) k
            (C_mono_argument s e0 (succ e0) _ (Or.inl (lt_succ_self e0)) k hp.2.1)
        · apply C_succ s _ _ e0 (lt_of_le_of_lt (zero_le _) (lt_succ_self _))
          exact C_mono_seed s _ _ _ (psi_mono s k e0 _ (Or.inl (lt_succ_self e0))) e0
            (C_mono_argument s e0 (succ e0) _ (Or.inl (lt_succ_self e0)) e0 hp.2.2)
      obtain ⟨_, _, hsC⟩ := C_proper_collapse_parameters s k (succ e0) A beta hp'
        (le_trans hbeta (psi_mono s k e0 _ (Or.inl (lt_succ_self e0)))) hnext.sub_C
      exact C_predecessor s A beta e0 hsC
    · -- A = succ (succ e0)
      subst h2
      by_cases hs : C s (succ (succ e0)) beta (succ e0)
      · exact C_predecessor s _ beta e0 hs
      · have hs' : ¬ C s (succ e0) beta (succ e0) := fun h =>
          hs (C_mono_argument s (succ e0) _ beta (Or.inl (lt_succ_self _)) _ h)
        have hx' := C_successor_of_argument_not_mem s (succ e0) beta hs' x hx
        exact C_mono_argument s (succ e0) _ beta (Or.inl (lt_succ_self _)) e0
          (C_barrier_succ s beta k e0 x hbeta hx' hlo hxk)
    · exact False.elim ((not_lt_iff_le _ _).mpr ((succ_le_iff_lt _ _).mpr h1) h2)
  · subst h1
    exact C_barrier_succ s beta k e0 x hbeta hx hlo hxk
  · exact False.elim ((not_lt_iff_le _ _).mpr ((succ_le_iff_lt _ _).mpr he0) h1)

end
end OCF.Denis
