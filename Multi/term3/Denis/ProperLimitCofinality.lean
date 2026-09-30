import Multi.term3.Denis.CollapseNormalization

/-! For a proper limit argument below the collapse index, actual
cofinality is preserved. The tail offset is an arbitrary ordinal here;
this theorem does not claim that it has a finite normal representation. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_limit_index_mem_at_stage (s : Supply) (k a length : O) (hl : 0 < length)
    (f : O → O) (hf : TransfiniteFundamentalSequence a length f)
    (hindex : C s a (psi s k a) k) :
    ∃ c, c < length ∧ C s (f c) (psi s k (f c)) k := by
  let g := fun i => psi s k (f i)
  have hfm : ∀ i j, i ≤ j → j < length → f i ≤ f j := fun _ _ => hf.mono
  have hgm : ∀ i j, i ≤ j → j < length → g i ≤ g j :=
    fun _ _ hij hj => psi_mono s k _ _ (hfm _ _ hij hj)
  have hsup : indexedSup length g = psi s k a := by
    rw [← psi_indexedSup s k length hl f hfm, hf.sup_eq]
  have hindex' : C s (indexedSup length f) (indexedSup length g) k := by
    rw [hf.sup_eq, hsup]
    exact hindex
  exact C_directed_indexedSup s length hl f g hfm hgm k hindex'

theorem psi_normal_limit_transfinite_tail (s : Supply) (k a length : O)
    (hk : RegularIndex s k) (hl : 0 < length) (hadd : AddPrincipal length)
    (f : O → O) (hf : TransfiniteFundamentalSequence a length f)
    (hbound : a < k) (hindex : C s a (psi s k a) k) (harg : C s a (psi s k a) a) :
    ∃ c, c < length ∧ TransfiniteFundamentalSequence (psi s k a) length
      (fun i => psi s k (f (c + i))) := by
  obtain ⟨c, hc, hkc⟩ := psi_limit_index_mem_at_stage s k a length hl f hf hindex
  have hshift := hf.shift c hadd hc
  refine ⟨c, hc, psi_transfiniteFundamentalSequence s k a length _ hk hl hshift
    (psi_tail_index_mem s k a length c f hf hadd hc hkc) ?_⟩
  exact fun i hi => C_seed s _ _ _ (psi_argument_normal_below s k a _ hbound harg (hshift.below i hi))

theorem psi_proper_limit_isLimit (s : Supply) (k a : O) (hk : RegularIndex s k) (ha : IsLimit a)
    (hbound : a < k) (hindex : C s a (psi s k a) k) (harg : C s a (psi s k a) a) :
    IsLimit (psi s k a) := by
  have hpos := lt_of_lt_of_le (finite_lt_omega 0) (omega_le_cofinality a ha)
  obtain ⟨_, _, hf⟩ := psi_normal_limit_transfinite_tail s k a (cofinality a ha) hk hpos
    (cofinality_addPrincipal a ha) _ (intrinsicSequence_spec a ha) hbound hindex harg
  exact hf.isLimit hpos

theorem psi_proper_limit_cofinality (s : Supply) (k a : O) (hk : RegularIndex s k) (ha : IsLimit a)
    (hbound : a < k) (hindex : C s a (psi s k a) k) (harg : C s a (psi s k a) a) :
    cofinality (psi s k a) (psi_proper_limit_isLimit s k a hk ha hbound hindex harg) = cofinality a ha := by
  have hpos := lt_of_lt_of_le (finite_lt_omega 0) (omega_le_cofinality a ha)
  obtain ⟨_, _, hf⟩ := psi_normal_limit_transfinite_tail s k a (cofinality a ha) hk hpos
    (cofinality_addPrincipal a ha) _ (intrinsicSequence_spec a ha) hbound hindex harg
  exact cofinality_eq_of_minimal_length ha hf

end
end OCF.Denis
