import Multi.term3.Denis.RegularArgumentSequences

/-! Proper collapses of composite limits with countable tails. The
whole argument need not lie below the collapse index. Closure of the
fixed parameter and a bound on the tail give eventual admissibility;
the parent's index membership gives eventual membership of the index. -/

namespace OCF.Denis
open Ordinal

theorem principal_eq_of_between_repeat {p x : O} (hx : AddPrincipal x) (n : Nat)
    (hpx : p ≤ x) (hxp : x < repeatAdd p n) : x = p := by
  rcases hpx with hpx | hpx
  · have bound (m : Nat) : repeatAdd p m < x := by
      induction m with
      | zero => exact lt_of_le_of_lt (zero_le p) hpx
      | succ m ih => exact hx p _ hpx ih
    exact False.elim (lt_asymm hxp (bound n))
  · exact hpx.symm

/-- Recover the leading principal value even with repeated equal
summands; the tail need not be smaller than that leading value. -/
theorem C_principal_of_lt_repeat (s : Supply) (a beta p x : O) (hp : AddPrincipal p) (n : Nat)
    (hx : C s a beta x) (hpx : p ≤ x) (hxp : x < repeatAdd p n) : C s a beta p := by
  have h := (C_iff s a beta x).mp hx
  clear hx
  induction h with
  | zero =>
    rw [le_antisymm hpx (zero_le p)]
    exact C_zero s a beta
  | seed hx => exact C_seed s a beta p (lt_of_le_of_lt hpx hx)
  | @add u v hu hv ihu ihv =>
    classical
    by_cases hpu : p ≤ u
    · exact ihu hpu (lt_of_le_of_lt (le_add u v) hxp)
    by_cases hpv : p ≤ v
    · exact ihv hpv (lt_of_le_of_lt (right_le_add u v) hxp)
    have hup : u < p := by
      rcases lt_total u p with hh | hh | hh
      · exact hh
      · exact False.elim (hpu (Or.inr hh.symm))
      · exact False.elim (hpu (Or.inl hh))
    have hvp : v < p := by
      rcases lt_total v p with hh | hh | hh
      · exact hh
      · exact False.elim (hpv (Or.inr hh.symm))
      · exact False.elim (hpv (Or.inl hh))
    exact False.elim (lt_irrefl _ (lt_of_le_of_lt hpx (hp u v hup hvp)))
  | @index q c hq hc ihq ihc =>
    have heq := principal_eq_of_between_repeat (I_addPrincipal s q c) n hpx hxp
    exact heq ▸ C_index s a beta q c ((C_iff s a beta q).mpr hq) ((C_iff s a beta c).mpr hc)
  | @collapse k c hc hk hkc hcc ihk ihc =>
    change p ≤ psi s k c at hpx
    change psi s k c < repeatAdd p n at hxp
    have heq := principal_eq_of_between_repeat (psi_addPrincipal s k c (regularIndex_regular s k hk)) n hpx hxp
    exact heq ▸ C_collapse s a beta k c hc hk ((C_iff s a beta k).mpr hkc) ((C_iff s a beta c).mpr hcc)

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem C_normal_sum_head (s : OCF.Denis.Supply) (cutoff beta : OCF.Denis.O) (p b : Term)
    (hn : IsNormal s (.add p b)) (hC : OCF.Denis.C s cutoff beta (denote s (.add p b))) :
    OCF.Denis.C s cutoff beta (denote s p) := by
  obtain ⟨n, hn'⟩ := normal_lt_repeat_leading s (.add p b) hn (by intro h; cases h)
  cases hn with
  | sum hp hb hpp hpv hbpos hhead =>
    change denote s (.add p b) < OCF.Denis.repeatAdd (denote s p.leading) n at hn'
    rw [leading_eq_of_principal p hpp] at hn'
    exact OCF.Denis.C_principal_of_lt_repeat s cutoff beta _ _ hpv n hC (le_add _ _) hn'

theorem proper_composite_countable_dense (s : OCF.Denis.Supply) (k a p b : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k)
    (f : Nat → OCF.Denis.O) (op : OCF.Denis.O → OCF.Denis.O)
    (hf : OCF.Denis.FundamentalSequence b f)
    (hF : OCF.Denis.FundamentalSequence a (fun n => op (f n)))
    (hfRep : ∀ n, Represented s (f n))
    (hopRep : ∀ x, Represented s x → Represented s (op x))
    (hb : b < OCF.Denis.psi s k a)
    (hp : OCF.Denis.C s a (OCF.Denis.psi s k a) p)
    (hK : OCF.Denis.C s a (OCF.Denis.psi s k a) k)
    (hop : ∀ u v x, OCF.Denis.C s u v p → OCF.Denis.C s u v x → OCF.Denis.C s u v (op x)) :
    DenseBelow s (OCF.Denis.psi s k a) := by
  obtain ⟨N, hN⟩ := OCF.Denis.composite_eventual_argument_normal s k a p b f op hf hF hb hp hop
  obtain ⟨M, hM⟩ := OCF.Denis.psi_limit_eventual_index_mem s k a
    (fun n => op (f (n + N))) (hF.shift N) hK
  have harg (n : Nat) := hN (n + M)
  have hseq := OCF.Denis.psi_fundamentalSequence s k a _ hk ((hF.shift N).shift M) hM harg
  exact dense_of_normal_sequence s _ _ hseq
    (fun n => represented_psi_of_mem s k _ hkRep (hopRep _ (hfRep ((n + M) + N))) hk (harg n))

theorem proper_sum_countable_dense (s : OCF.Denis.Supply) (k p b : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k) (hpRep : Represented s p)
    (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hbnd : b < OCF.Denis.psi s k (p + b))
    (hp : OCF.Denis.C s (p + b) (OCF.Denis.psi s k (p + b)) p)
    (hK : OCF.Denis.C s (p + b) (OCF.Denis.psi s k (p + b)) k) :
    DenseBelow s (OCF.Denis.psi s k (p + b)) := by
  let f := revisedValue s b
  have hf := revised_fundamentalSequence_of_dense s b ((zero_lt_iff_ne_zero b).mpr hb.1) hd
  exact proper_composite_countable_dense s k (p + b) p b hk hkRep f (fun x => p + x)
    hf (OCF.Denis.add_fundamentalSequence p b f hf) (revisedValue_represented s b)
    (fun x hx => represented_add s p x hpRep hx) hbnd hp hK
    (fun u v x hpu hx => OCF.Denis.C_add s u v p x hpu hx)

theorem proper_normal_sum_countable_dense (s : OCF.Denis.Supply) (k p b : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k) (hpRep : Represented s p)
    (hpp : AddPrincipal p) (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hbp : b < p) (hbk : b < k)
    (hK : OCF.Denis.C s (p + b) (OCF.Denis.psi s k (p + b)) k)
    (harg : OCF.Denis.C s (p + b) (OCF.Denis.psi s k (p + b)) (p + b)) :
    DenseBelow s (OCF.Denis.psi s k (p + b)) := by
  have hbC := OCF.Denis.C_suffix s _ _ (p + b) p b harg rfl
  have hpC := OCF.Denis.C_principal_prefix s _ _ p b hpp hbp harg
  exact proper_sum_countable_dense s k p b hk hkRep hpRep hb hd
    (OCF.Denis.psi_closed s k _ b hbC hbk) hpC hK

theorem proper_I_countable_dense (s : OCF.Denis.Supply) (k r b : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k) (hrRep : Represented s r)
    (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hbnd : b < OCF.Denis.psi s k (OCF.Denis.I s r b))
    (hr : OCF.Denis.C s (OCF.Denis.I s r b) (OCF.Denis.psi s k (OCF.Denis.I s r b)) r)
    (hK : OCF.Denis.C s (OCF.Denis.I s r b) (OCF.Denis.psi s k (OCF.Denis.I s r b)) k) :
    DenseBelow s (OCF.Denis.psi s k (OCF.Denis.I s r b)) := by
  let f := revisedValue s b
  have hf := revised_fundamentalSequence_of_dense s b ((zero_lt_iff_ne_zero b).mpr hb.1) hd
  exact proper_composite_countable_dense s k (OCF.Denis.I s r b) r b hk hkRep f (OCF.Denis.I s r)
    hf (OCF.Denis.I_fundamentalSequence s r b f hf) (revisedValue_represented s b)
    (fun x hx => represented_I s r x hrRep hx) hbnd hr hK
    (fun u v x hru hx => OCF.Denis.C_index s u v r x hru hx)

theorem proper_normal_I_countable_dense (s : OCF.Denis.Supply) (k r b : OCF.Denis.O)
    (hk : OCF.Denis.RegularIndex s k) (hkRep : Represented s k) (hrRep : Represented s r)
    (hb : OCF.Denis.IsLimit b) (hd : DenseBelow s b)
    (hrI : r < OCF.Denis.I s r b) (hbI : b < OCF.Denis.I s r b) (hbk : b < k)
    (hK : OCF.Denis.C s (OCF.Denis.I s r b) (OCF.Denis.psi s k (OCF.Denis.I s r b)) k)
    (harg : OCF.Denis.C s (OCF.Denis.I s r b) (OCF.Denis.psi s k (OCF.Denis.I s r b)) (OCF.Denis.I s r b)) :
    DenseBelow s (OCF.Denis.psi s k (OCF.Denis.I s r b)) := by
  obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ r b hrI hbI harg
  exact proper_I_countable_dense s k r b hk hkRep hrRep hb hd
    (OCF.Denis.psi_closed s k _ b hbC hbk) hrC hK

end
end T.Correspondence.Denis.Covering
