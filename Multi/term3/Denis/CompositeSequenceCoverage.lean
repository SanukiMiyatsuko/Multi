import Multi.term3.Denis.RankSequenceCoverage

/-! Ordinal-length composite limit rules. Represented bounds on the
fixed parameter and the variable tail allow a represented offset,
even when the complete argument is above the collapse index. -/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem proper_composite_coveringFundamentalSequence (s : OCF.Denis.Supply) (k a : Term)
    (hn : IsNormal s (.psi k a))
    (hK : OCF.Denis.C s (denote s a) (denote s (.psi k a)) (denote s k))
    (p b length : OCF.Denis.O) (hpRep : Represented s p) (hbRep : Represented s b)
    (hp : p < denote s (.psi k a)) (hb : b < denote s (.psi k a))
    (hl : 0 < length) (hadd : AddPrincipal length)
    (f op : OCF.Denis.O → OCF.Denis.O) (hf : OCF.Denis.TransfiniteFundamentalSequence b length f)
    (hF : CoveringFundamentalSequence s (denote s a) length (fun i => op (f i)))
    (hop : ∀ u v x, OCF.Denis.C s u v p → OCF.Denis.C s u v x → OCF.Denis.C s u v (op x)) :
    ∃ c, Represented s c ∧ c < length ∧
      CoveringFundamentalSequence s (denote s (.psi k a)) length
        (fun i => OCF.Denis.psi s (denote s k) (op (f (c + i)))) := by
  have halim := hF.normalSequence.fundamental.isLimit hl
  obtain ⟨dK, hdK, hdKa, hstage⟩ := proper_index_mem_at_represented_stage s k a hn halim hK
  have hreg : OCF.Denis.RegularIndex s (denote s k) := by cases hn; assumption
  obtain ⟨d, hd, hda, hpd, hbd⟩ := combine_represented_stages s (denote s a) p b
    (OCF.Denis.psi s (denote s k)) (fun _ _ h => OCF.Denis.psi_mono s _ _ _ h)
    (represented_limit_collapse_interpolation s _ _ p hreg halim hpRep hp)
    (represented_limit_collapse_interpolation s _ _ b hreg halim hbRep hb)
  obtain ⟨u, hu, hua, hdu, hdKu⟩ := combine_represented_stages s (denote s a) d dK (fun x => x)
    (fun _ _ h => h)
    ⟨succ d, represented_succ s d hd, OCF.Denis.succ_lt_limit halim hda, lt_succ_self d⟩
    ⟨succ dK, represented_succ s dK hdK, OCF.Denis.succ_lt_limit halim hdKa, lt_succ_self dK⟩
  obtain ⟨c, hc, hcl, huc⟩ := hF.cofinal_normal u hu hua
  have hdc := OCF.Ordinal.lt_trans _ _ _ hdu huc
  have hdKc := OCF.Ordinal.lt_trans _ _ _ hdKu huc
  have hindex : OCF.Denis.C s (op (f c)) (OCF.Denis.psi s (denote s k) (op (f c))) (denote s k) :=
    OCF.Denis.C_mono_seed s _ _ _ (OCF.Denis.psi_mono s _ _ _ (Or.inl hdKc)) _
      (OCF.Denis.C_mono_argument s _ _ _ (Or.inl hdKc) _ hstage)
  have hshift := hF.shift c hadd hcl hc
  cases hn with
  | collapse hk ha hreg harg =>
    refine ⟨c, hc, hcl, psi_coveringFundamentalSequence s _ _ length ⟨k, hk, rfl⟩ hreg hl _ hshift ?_ ?_⟩
    · exact OCF.Denis.psi_tail_index_mem s _ _ length c (fun i => op (f i))
        hF.normalSequence.fundamental hadd hcl hindex
    · intro i hi
      have hmono := hF.normalSequence.fundamental.mono (le_add c i) (hadd c i hcl hi)
      have hseed := OCF.Denis.psi_mono s (denote s k) d (op (f (c + i)))
        (Or.inl (OCF.Ordinal.lt_of_lt_of_le hdc hmono))
      exact hop _ _ _ (OCF.Denis.C_seed s _ _ _ (OCF.Ordinal.lt_of_lt_of_le hpd hseed))
        (OCF.Denis.C_seed s _ _ _ (OCF.Ordinal.lt_trans _ _ _ (hf.below _ (hadd c i hcl hi))
          (OCF.Ordinal.lt_of_lt_of_le hbd hseed)))

theorem proper_I_small_parameters_coveringFundamentalSequence (s : OCF.Denis.Supply) (k r b : Term)
    (hn : IsNormal s (.psi k (.I r b)))
    (hK : OCF.Denis.C s (denote s (.I r b)) (denote s (.psi k (.I r b))) (denote s k))
    (hrk : denote s r < denote s k) (hbk : denote s b < denote s k)
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
      exact proper_composite_coveringFundamentalSequence s k (.I r b) hparent hK
        (denote s r) (denote s b) length ⟨r, hr, rfl⟩ ⟨b, hb, rfl⟩
        (OCF.Denis.psi_closed s _ _ _ hrC hrk) (OCF.Denis.psi_closed s _ _ _ hbC hbk)
        hl hadd f (OCF.Denis.I s (denote s r)) hf.normalSequence.fundamental
        (I_coveringFundamentalSequence s _ _ length ⟨r, hr, rfl⟩ hl f hf)
        (fun u v x hru hx => OCF.Denis.C_index s u v _ x hru hx)

end
end T.Correspondence.Denis.Covering
