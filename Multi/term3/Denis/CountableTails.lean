import Multi.term3.Denis.ClosureSubterms

/-! Limit arguments with a countable tail. A finite initial segment may
fail admissibility; finitariness of C supplies an offset after which all
arguments are normal. Cofinality is preserved by that shift. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem composite_eventual_argument_normal (s : Supply) (k a p b : O)
    (f : Nat → O) (op : O → O) (hf : FundamentalSequence b f)
    (hF : FundamentalSequence a (fun n => op (f n)))
    (hb : b < psi s k a) (hp : C s a (psi s k a) p)
    (hop : ∀ u v x, C s u v p → C s u v x → C s u v (op x)) :
    ∃ N, ∀ n, C s (op (f (n + N))) (psi s k (op (f (n + N)))) (op (f (n + N))) := by
  let F := fun n => op (f n)
  let g := fun n => psi s k (F n)
  have hFm : ∀ n m, n ≤ m → F n ≤ F m := fun _ _ h => hF.mono h
  have hgm : ∀ n m, n ≤ m → g n ≤ g m := fun n m h => psi_mono s k _ _ (hFm n m h)
  have hsup : sup g = psi s k a := by
    rw [← psi_sup s k F hFm]
    exact congrArg (psi s k) hF.sup_eq
  have hp' : C s (sup F) (sup g) p := by
    rw [hF.sup_eq, hsup]
    exact hp
  obtain ⟨Np, hNp⟩ := C_directed_sup s F g hFm hgm p hp'
  have hb' : b < sup g := hsup ▸ hb
  obtain ⟨Nb, hNb⟩ := (lt_sup_iff g b).mp hb'
  refine ⟨max Np Nb, fun n => ?_⟩
  have hnp : Np ≤ n + max Np Nb := by omega
  have hnb : Nb ≤ n + max Np Nb := by omega
  have hpC : C s (F (n + max Np Nb)) (g (n + max Np Nb)) p :=
    C_mono_seed s _ _ _ (hgm _ _ hnp) p (C_mono_argument s _ _ _ (hFm _ _ hnp) p hNp)
  have hbnd := lt_of_lt_of_le hNb (hgm _ _ hnb)
  exact hop _ _ _ hpC (C_seed s _ _ _ (lt_trans _ _ _ (hf.below _) hbnd))

end
end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem psi_first_sum_limit_dense (s : OCF.Denis.Supply) (p b : OCF.Denis.O)
    (hp : Represented s p) (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hbnd : b < OCF.Denis.psi s (OCF.Denis.I s 0 0) (p + b))
    (hpC : OCF.Denis.C s (p + b) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (p + b)) p) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (p + b)) := by
  let f := revisedValue s b
  have hf := revised_fundamentalSequence_of_dense s b ((zero_lt_iff_ne_zero b).mpr hb.1) hd
  have hF := OCF.Denis.add_fundamentalSequence p b f hf
  obtain ⟨N, hN⟩ := OCF.Denis.composite_eventual_argument_normal s (OCF.Denis.I s 0 0)
    (p + b) p b f (fun x => p + x) hf hF hbnd hpC
    (fun u v x hpu hx => OCF.Denis.C_add s u v p x hpu hx)
  have hpsi := OCF.Denis.psi_fundamentalSequence s (OCF.Denis.I s 0 0) (p + b)
    (fun n => p + f (n + N)) (Or.inl ⟨0, rfl⟩) (hF.shift N)
    (fun _ => OCF.Denis.first_mem_C s _ _) hN
  apply dense_of_normal_sequence s _ _ hpsi
  intro n
  exact represented_psi_of_mem s _ _ ⟨omega1, omega1_isNormal s, rfl⟩
    (represented_add s p _ hp (revisedValue_represented s b (n + N))) (Or.inl ⟨0, rfl⟩) (hN n)

/-- The premises on the constant principal head and countable tail follow
from the normal form of the parent argument. -/
theorem psi_first_normal_sum_limit_dense (s : OCF.Denis.Supply) (p b : OCF.Denis.O)
    (hp : Represented s p) (hpp : AddPrincipal p) (hb : OCF.Denis.IsLimit b)
    (hbp : b < p) (hbk : b < OCF.Denis.I s 0 0) (hd : DenseBelow s b)
    (harg : OCF.Denis.C s (p + b) (OCF.Denis.psi s (OCF.Denis.I s 0 0) (p + b)) (p + b)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (p + b)) := by
  have hbC := OCF.Denis.C_suffix s _ _ (p + b) p b harg rfl
  have hpC := OCF.Denis.C_principal_prefix s _ _ p b hpp hbp harg
  exact psi_first_sum_limit_dense s p b hp hb hd (OCF.Denis.psi_closed s _ _ b hbC hbk) hpC

theorem psi_first_I_limit_dense (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hbnd : b < OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b))
    (hrC : OCF.Denis.C s (OCF.Denis.I s r b)
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b)) r) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b)) := by
  let f := revisedValue s b
  have hf := revised_fundamentalSequence_of_dense s b ((zero_lt_iff_ne_zero b).mpr hb.1) hd
  have hF := OCF.Denis.I_fundamentalSequence s r b f hf
  obtain ⟨N, hN⟩ := OCF.Denis.composite_eventual_argument_normal s (OCF.Denis.I s 0 0)
    (OCF.Denis.I s r b) r b f (fun x => OCF.Denis.I s r x) hf hF hbnd hrC
    (fun u v x hru hx => OCF.Denis.C_index s u v r x hru hx)
  have hpsi := OCF.Denis.psi_fundamentalSequence s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b)
    (fun n => OCF.Denis.I s r (f (n + N))) (Or.inl ⟨0, rfl⟩) (hF.shift N)
    (fun _ => OCF.Denis.first_mem_C s _ _) hN
  apply dense_of_normal_sequence s _ _ hpsi
  intro n
  exact represented_psi_of_mem s _ _ ⟨omega1, omega1_isNormal s, rfl⟩
    (represented_I s r _ hr (revisedValue_represented s b (n + N))) (Or.inl ⟨0, rfl⟩) (hN n)

theorem psi_first_normal_I_limit_dense (s : OCF.Denis.Supply) (r b : OCF.Denis.O)
    (hr : Represented s r) (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hrI : r < OCF.Denis.I s r b) (hbI : b < OCF.Denis.I s r b) (hbk : b < OCF.Denis.I s 0 0)
    (harg : OCF.Denis.C s (OCF.Denis.I s r b)
      (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b)) (OCF.Denis.I s r b)) :
    DenseBelow s (OCF.Denis.psi s (OCF.Denis.I s 0 0) (OCF.Denis.I s r b)) := by
  obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ r b hrI hbI harg
  exact psi_first_I_limit_dense s r b hr hb hd (OCF.Denis.psi_closed s _ _ b hbC hbk) hrC

end
end T.Correspondence.Denis.Covering
