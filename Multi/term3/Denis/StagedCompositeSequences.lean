import Multi.term3.Denis.ClosureStageApproximation

/-! Composite limit sequences with a fixed parameter supported at a
represented earlier closure stage. The fixed parameter may exceed the
outer collapse index; the variable tail remains below that index. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem proper_staged_composite_coveringFundamentalSequence (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a))
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k))
    (p b length : OCF.Denis.O) (hpStage : RepresentedClosureStage s (denote s k) (denote s a) p)
    (hbRep : Represented s b) (hb : b < denote s (.psi k a))
    (hl : 0 < length) (hadd : AddPrincipal length)
    (f op : OCF.Denis.O → OCF.Denis.O) (hf : OCF.Denis.TransfiniteFundamentalSequence b length f)
    (hF : CoveringFundamentalSequence s (denote s a) length (fun i => op (f i)))
    (hop : ∀ u v x, OCF.Denis.C s u v p → OCF.Denis.C s u v x → OCF.Denis.C s u v (op x)) :
    ∃ c, Represented s c ∧ c < length ∧
      CoveringFundamentalSequence s (denote s (.psi k a)) length
        (fun i => OCF.Denis.psi s (denote s k) (op (f (c + i)))) := by
  have halim := hF.normalSequence.fundamental.isLimit hl
  have hreg : OCF.Denis.RegularIndex s (denote s k) := by cases hn; assumption
  obtain ⟨d, hd, hda, hpd, hKd⟩ := representedClosureStage_pair s (denote s k) (denote s a) p _ hpStage
    (proper_index_mem_at_represented_stage s k a hn halim hK)
  obtain ⟨e, he, hea, hbe⟩ := represented_limit_collapse_interpolation s _ _ b hreg halim hbRep hb
  obtain ⟨u, hu, hua, hdu, heu⟩ := combine_represented_stages s (denote s a) d e (fun x => x)
    (fun _ _ h => h)
    ⟨succ d, represented_succ s d hd, OCF.Denis.succ_lt_limit halim hda, lt_succ_self d⟩
    ⟨succ e, represented_succ s e he, OCF.Denis.succ_lt_limit halim hea, lt_succ_self e⟩
  obtain ⟨c, hc, hcl, huc⟩ := hF.cofinal_normal u hu hua
  have hdc := OCF.Ordinal.lt_trans _ _ _ hdu huc
  have hec := OCF.Ordinal.lt_trans _ _ _ heu huc
  have hindex := closure_stage_mono s (denote s k) d (op (f c)) _ (Or.inl hdc) hKd
  have hshift := hF.shift c hadd hcl hc
  cases hn with
  | collapse hk ha hreg harg =>
    refine ⟨c, hc, hcl, psi_coveringFundamentalSequence s _ _ length ⟨k, hk, rfl⟩ hreg hl _ hshift ?_ ?_⟩
    · exact OCF.Denis.psi_tail_index_mem s _ _ length c (fun i => op (f i))
        hF.normalSequence.fundamental hadd hcl hindex
    · intro i hi
      have hmono := hF.normalSequence.fundamental.mono (le_add c i) (hadd c i hcl hi)
      have hseed := OCF.Denis.psi_mono s (denote s k) e (op (f (c + i)))
        (Or.inl (OCF.Ordinal.lt_of_lt_of_le hec hmono))
      exact hop _ _ _
        (closure_stage_mono s (denote s k) d _ p (Or.inl (OCF.Ordinal.lt_of_lt_of_le hdc hmono)) hpd)
        (OCF.Denis.C_seed s _ _ _ (OCF.Ordinal.lt_trans _ _ _ (hf.below _ (hadd c i hcl hi))
          (OCF.Ordinal.lt_of_lt_of_le hbe hseed)))

theorem proper_I_tree_parameter_coveringFundamentalSequence (s : OCF.Denis.Supply) (k r b : Term)
    (hn : IsNormal s (.psi k (.I r b)))
    (hK : OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k))
    (hrTree : CollapseTree s r) (hbk : denote s b < denote s k)
    (length : OCF.Denis.O) (hl : 0 < length) (hadd : AddPrincipal length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s (denote s b) length f) :
    ∃ c, Represented s c ∧ c < length ∧
      CoveringFundamentalSequence s (denote s (.psi k (.I r b))) length
        (fun i => OCF.Denis.psi s (denote s k) (OCF.Denis.I s (denote s r) (f (c + i)))) := by
  have hparent := hn
  cases hn with
  | collapse hk ha hreg harg =>
    cases ha with
    | index hr hb hrl hbl =>
      obtain ⟨hrC, hbC⟩ := OCF.Denis.C_normal_index_parameters s _ _ _ _ hrl hbl harg
      have hF := I_coveringFundamentalSequence s _ _ length ⟨r, hr, rfl⟩ hl f hf
      exact proper_staged_composite_coveringFundamentalSequence s k (.I r b) hparent hK
        (denote s r) (denote s b) length
        (hrTree.representedClosureStage _ _ hreg (hF.normalSequence.fundamental.isLimit hl) hrC)
        ⟨b, hb, rfl⟩ (OCF.Denis.psi_closed s _ _ _ hbC hbk) hl hadd f (OCF.Denis.I s (denote s r))
        hf.normalSequence.fundamental hF (fun u v x hru hx => OCF.Denis.C_index s u v _ x hru hx)

theorem proper_sum_tree_parameter_coveringFundamentalSequence (s : OCF.Denis.Supply) (k p b : Term)
    (hn : IsNormal s (.psi k (.add p b)))
    (hK : OCF.Denis.C s (denote s (.add p b)) (denote s (.psi k (.add p b))) (denote s k))
    (hpTree : CollapseTree s p) (hbk : denote s b < denote s k)
    (length : OCF.Denis.O) (hl : 0 < length) (hadd : AddPrincipal length)
    (f : OCF.Denis.O → OCF.Denis.O) (hf : CoveringFundamentalSequence s (denote s b) length f) :
    ∃ c, Represented s c ∧ c < length ∧
      CoveringFundamentalSequence s (denote s (.psi k (.add p b))) length
        (fun i => OCF.Denis.psi s (denote s k) (denote s p + f (c + i))) := by
  have hparent := hn
  cases hn with
  | collapse hk ha hreg harg =>
    obtain ⟨hpC, hbC⟩ := C_normal_sum_components s _ _ p b ha harg
    cases ha with
    | sum hp hb hpp hpv hbpos hhead =>
      have hF := add_coveringFundamentalSequence s _ _ length ⟨p, hp, rfl⟩ hl f hf
      exact proper_staged_composite_coveringFundamentalSequence s k (.add p b) hparent hK
        (denote s p) (denote s b) length
        (hpTree.representedClosureStage _ _ hreg (hF.normalSequence.fundamental.isLimit hl) hpC)
        ⟨b, hb, rfl⟩ (OCF.Denis.psi_closed s _ _ _ hbC hbk) hl hadd f (fun x => denote s p + x)
        hf.normalSequence.fundamental hF (fun u v x hpu hx => OCF.Denis.C_add s u v _ x hpu hx)

end
end T.Correspondence.Denis.Covering
