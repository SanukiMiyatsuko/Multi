import Multi.term3.Denis.SuccessorIndexArguments

/-! A countable normal limit below a regular collapse index. Membership
of the index at the parent suffices: finitariness recovers membership
along a tail. No index-membership assumption is made at argument zero. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem psi_limit_eventual_index_mem (s : Supply) (k a : O) (f : Nat → O)
    (hf : FundamentalSequence a f) (hk : C s a (psi s k a) k) :
    ∃ N, ∀ n, C s (f (n + N)) (psi s k (f (n + N))) k := by
  let g := fun n => psi s k (f n)
  have hfm : ∀ n m, n ≤ m → f n ≤ f m := fun _ _ h => hf.mono h
  have hgm : ∀ n m, n ≤ m → g n ≤ g m := fun n m h => psi_mono s k _ _ (hfm n m h)
  have hsup : sup g = psi s k a := by
    rw [← psi_sup s k f hfm, hf.sup_eq]
  have hk' : C s (sup f) (sup g) k := by
    rw [hf.sup_eq, hsup]
    exact hk
  obtain ⟨N, hN⟩ := C_directed_sup s f g hfm hgm k hk'
  refine ⟨N, fun n => ?_⟩
  have hle : N ≤ n + N := Nat.le_add_left N n
  exact C_mono_seed s _ _ _ (hgm _ _ hle) k (C_mono_argument s _ _ _ (hfm _ _ hle) k hN)

theorem psi_normal_limit_shift_fundamentalSequence (s : Supply) (k a : O) (f : Nat → O)
    (hk : RegularIndex s k) (hf : FundamentalSequence a f) (ha : a < k)
    (hindex : C s a (psi s k a) k) (harg : C s a (psi s k a) a) :
    ∃ N, FundamentalSequence (psi s k a) (fun n => psi s k (f (n + N))) := by
  obtain ⟨N, hN⟩ := psi_limit_eventual_index_mem s k a f hf hindex
  exact ⟨N, psi_fundamentalSequence s k a _ hk (hf.shift N) hN
    (fun n => C_seed s _ _ _ (psi_argument_normal_below s k a _ ha harg (hf.below _)))⟩

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem psi_normal_countable_limit_dense (s : OCF.Denis.Supply) (k a : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k)
    (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a) (hbound : a < k)
    (hindex : OCF.Denis.C s a (OCF.Denis.psi s k a) k)
    (harg : OCF.Denis.C s a (OCF.Denis.psi s k a) a) :
    DenseBelow s (OCF.Denis.psi s k a) := by
  let f := revisedValue s a
  have hf := revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd
  obtain ⟨N, hN⟩ := OCF.Denis.psi_normal_limit_shift_fundamentalSequence s k a f hk hf hbound hindex harg
  apply dense_of_normal_sequence s _ _ hN
  intro n
  exact represented_psi_of_mem s k _ hkRep (revisedValue_represented s a (n + N)) hk
    (OCF.Denis.C_seed s _ _ _ (OCF.Denis.psi_argument_normal_below s k a _ hbound harg (hf.below _)))

end
end T.Correspondence.Denis.Covering
