import Multi.term3.Denis.UniformStageLimit

/-! The uniform stage bound at a proper collapse with argument zero or a
successor.

Let `x = psi π e` be isolated in `Y = C(A, psi k A)`, `(π, e)` proper,
`π = I(λ, ζ)` and `e` zero or a successor. Let `σ` be the supremum of `Y`
below `x`. By minimality of `x`, the closure `C(e, σ)` has a least element
in `[σ, π)`. Its canonical form forces an `I` value `I(b1, b2)` in
`[σ, x)` with `b1, b2 < σ`; then `b1 < λ` and `Y` has no element in
`[b1, λ)`. So `λ` is a limit isolated in `Y`, and with the bound `wλ` for
`λ` the bound for `x` is `I(wλ, L + 1)`, where `L` collects the remaining
parameters below `x`. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem ustage_psi_rank (s : Supply) (π e lam zeta : O) (hp : ProperCollapse s π e)
    (he : e = 0 ∨ ∃ e', e = succ e') (hπI : π = I s lam zeta) (hlam : lam < π)
    (hzeta : zeta < π) (ih : UStage s lam) : UStage s (psi s π e) := by
  intro k A y hk hxY hiso hyA
  have hπreg := regularIndex_regular s π hp.1
  have hxπ : psi s π e < π := psi_lt s π e hπreg
  have hBx : psi s k A < psi s π e := hiso.seed_lt
  obtain ⟨heA, hπY, heY⟩ := C_proper_collapse_parameters s π e A _ hp (Or.inl hBx) hxY
  have hlaml : lam < I s lam zeta := by rw [← hπI]; exact hlam
  have hzetal : zeta < I s lam zeta := by rw [← hπI]; exact hzeta
  have hπC : C s e (psi s π e) (I s lam zeta) := by rw [← hπI]; exact hp.2.1
  obtain ⟨hlamC, hzetaC⟩ := C_normal_index_parameters s e _ lam zeta hlaml hzetal hπC
  have hlamx : lam < psi s π e := psi_closed s π e lam hlamC hlam
  have hzetax : zeta < psi s π e := psi_closed s π e zeta hzetaC hzeta
  have hπY' : C s A (psi s k A) (I s lam zeta) := by rw [← hπI]; exact hπY
  obtain ⟨hlamY, hzetaY⟩ := C_normal_index_parameters s A _ lam zeta hlaml hzetal hπY'
  have hπreg' : UncountableRegular (I s lam zeta) := by rw [← hπI]; exact hπreg
  have hzcases := regular_I_argument s lam zeta hzetal hπreg'
  have hxlim : IsLimit (psi s π e) := hiso.1
  have hxprin := psi_addPrincipal s π e hπreg
  -- the value at the predecessor of the argument
  have hpred : ∀ e', e = succ e' →
      C s A (psi s k A) (psi s π e') ∧ psi s π e' < psi s π e := by
    intro e' he'
    have heY' : C s A (psi s k A) (succ e') := by rw [← he']; exact heY
    have he'Y : C s A _ e' := C_predecessor s A _ e' heY'
    have he'e : e' < e := by rw [he']; exact lt_succ_self e'
    refine ⟨C_collapse s A _ π e' (lt_trans _ _ _ he'e heA) hp.1 hπY he'Y, ?_⟩
    rcases psi_mono s π e' e (Or.inl he'e) with h | h
    · exact h
    · exfalso
      obtain ⟨_, _, hgap⟩ := psi_proper_plateau s π e π e' hp.1 hp.1 hp.2.1 hp.2.2 h
      have heC : C s e (psi s π e) (succ e') := by rw [← he']; exact hp.2.2
      exact hgap e' (C_predecessor s e _ e' heC) (le_refl e') he'e
  -- Step A: the rank is a limit isolated in the closure
  have hlamiso : IsoIn s A (psi s k A) lam := by
    classical
    obtain ⟨_, c, hcx, hc⟩ := hiso
    have hσY := supBelow_bound s A (psi s k A) (psi s π e)
    have hσx : supBelow s A (psi s k A) (psi s π e) < psi s π e :=
      lt_of_le_of_lt (supBelow_le s A _ _ c
        (fun d hd hdx => lt_of_not_ge' (fun hcd => hc d hd hcd hdx))) hcx
    have hσprin := supBelow_addPrincipal s A (psi s k A) (psi s π e) hxprin
    have hσcof := supBelow_cofinal s A (psi s k A) (psi s π e)
    have hσpos : 0 < supBelow s A (psi s k A) (psi s π e) :=
      hσY 0 (C_zero s _ _) (lt_of_le_of_lt (zero_le _) hBx)
    generalize supBelow s A (psi s k A) (psi s π e) = σ at hσY hσx hσprin hσcof hσpos
    -- an element of `C(e, σ)` in `[σ, π)`
    have hexb : ∃ b, C s e σ b ∧ b < π ∧ σ ≤ b := by
      apply Classical.byContradiction
      intro hno
      apply (not_lt_iff_le _ _).mpr _ hσx
      apply psi_min s π e σ
      refine ⟨Or.inl (lt_trans _ _ _ hσx hxπ), fun b hb hbπ => ?_⟩
      exact lt_of_not_ge' (fun hσb => hno ⟨b, hb, hbπ, hσb⟩)
    have hbspec := least_spec _ hexb
    generalize least (fun b => C s e σ b ∧ b < π ∧ σ ≤ b) hexb = b at hbspec
    obtain ⟨⟨hbC, hbπ, hσb⟩, hbmin⟩ := hbspec
    have hsmall : ∀ u, u < b → C s e σ u → u < σ := by
      intro u hub huC
      apply lt_of_not_ge'
      intro hσu
      exact hbmin u hub ⟨huC, lt_trans _ _ _ hub hbπ, hσu⟩
    have hbx : b < psi s π e :=
      psi_closed s π e b (C_mono_seed s e σ _ (Or.inl hσx) b hbC) hbπ
    -- an `I` value in `[σ, x)` with parameters below `σ` isolates the rank
    have Ilem : ∀ b1 b2, σ ≤ I s b1 b2 → I s b1 b2 < psi s π e → b1 < σ → b2 < σ →
        IsoIn s A (psi s k A) lam := by
      intro b1 b2 hσI hIx hb1 hb2
      obtain ⟨d2, hd2Y, hd2x, hb2d2⟩ := hσcof b2 hb2
      have hIπ : I s b1 b2 < I s lam zeta := by rw [← hπI]; exact lt_trans _ _ _ hIx hxπ
      rcases I_lt_cases s b1 b2 lam zeta hIπ with ⟨hb1l, _⟩ | ⟨hb1l, hb2z⟩ | ⟨_, hIz⟩
      · have hgap : ∀ d, C s A (psi s k A) d → b1 ≤ d → d < lam → False := by
          intro d hd hb1d hdl
          have hd2π : d2 < I s lam zeta := by rw [← hπI]; exact lt_trans _ _ _ hd2x hxπ
          have htπ : I s d d2 < I s lam zeta := by
            rw [← I_rank_fixed s d lam zeta hdl]
            exact I_strict s d hd2π
          have htC : C s e (psi s π e) (I s d d2) :=
            C_index s e _ d d2 (C_seed s e _ d (lt_trans _ _ _ hdl hlamx)) (C_seed s e _ d2 hd2x)
          have htx : I s d d2 < psi s π e :=
            psi_closed s π e _ htC (by rw [hπI]; exact htπ)
          have htσ := hσY _ (C_index s A _ d d2 hd hd2Y) htx
          exact (not_lt_iff_le _ _).mpr (le_trans hσI (I_mono_both s hb1d hb2d2)) htσ
        refine ⟨⟨fun h0 => ?_, fun ⟨l', hl'⟩ => ?_⟩, b1, hb1l, hgap⟩
        · rw [h0] at hb1l
          exact not_lt_zero _ hb1l
        · have hlamY' : C s A (psi s k A) (succ l') := by rw [← hl']; exact hlamY
          have hl'Y : C s A _ l' := C_predecessor s A _ l' hlamY'
          have hb1l' : b1 ≤ l' := by
            rw [hl'] at hb1l
            exact (lt_succ_iff_le _ _).mp hb1l
          exact hgap l' hl'Y hb1l' (by rw [hl']; exact lt_succ_self l')
      · exfalso
        rcases hzcases with hz0 | ⟨z', hz'⟩
        · rw [hz0] at hb2z
          exact not_lt_zero _ hb2z
        · have hzetaY' : C s A (psi s k A) (succ z') := by rw [← hz']; exact hzetaY
          have hz'Y : C s A _ z' := C_predecessor s A _ z' hzetaY'
          have hb2z' : b2 ≤ z' := by
            rw [hz'] at hb2z
            exact (lt_succ_iff_le _ _).mp hb2z
          have hz'x : z' < psi s π e := by
            apply lt_trans _ _ _ _ hzetax
            rw [hz']
            exact lt_succ_self z'
          have htπ : I s lam z' < π := by
            rw [hπI, hz']
            exact I_strict s lam (lt_succ_self z')
          have htC : C s e (psi s π e) (I s lam z') :=
            C_index s e _ lam z' (C_seed s e _ lam hlamx) (C_seed s e _ z' hz'x)
          have htx := psi_closed s π e _ htC htπ
          have htσ := hσY _ (C_index s A _ lam z' hlamY hz'Y) htx
          rw [hb1l] at hσI
          exact (not_lt_iff_le _ _).mpr (le_trans hσI (I_mono s lam hb2z')) htσ
      · exfalso
        have hzσ := hσY zeta hzetaY hzetax
        exact (not_lt_iff_le _ _).mpr hσI (lt_trans _ _ _ hIz hzσ)
    rcases C_canonical s e σ b hbC with h0 | hseed | ⟨u, v, rfl, hub, hvb, huC, hvC⟩ |
        ⟨b1, b2, rfl, hb1, hb2, hb1C, hb2C⟩ | ⟨ρ, f, rfl, hfe, hρf, hρC, _⟩
    · exfalso
      rw [h0] at hσb
      exact (not_lt_iff_le _ _).mpr hσb hσpos
    · exact False.elim ((not_lt_iff_le _ _).mpr hσb hseed)
    · exact False.elim ((not_lt_iff_le _ _).mpr hσb
        (hσprin u v (hsmall u hub huC) (hsmall v hvb hvC)))
    · exact Ilem b1 b2 hσb hbx (hsmall b1 hb1 hb1C) (hsmall b2 hb2 hb2C)
    · have hρreg := regularIndex_regular s ρ hρf.1
      have hbρ : psi s ρ f < ρ := psi_lt s ρ f hρreg
      rcases lt_total ρ π with hρπ | hρπ | hπρ
      · obtain ⟨r', z', hρI, hr'ρ, hz'ρ, hr'C, hz'C⟩ :=
          C_regular_normal_presentation s e σ ρ hρreg (le_trans hσb (Or.inl hbρ)) hρC
        have hρfC : C s f (psi s ρ f) (I s r' z') := by rw [← hρI]; exact hρf.2.1
        obtain ⟨hr'f, hz'f⟩ := C_normal_index_parameters s f _ r' z'
          (by rw [← hρI]; exact hr'ρ) (by rw [← hρI]; exact hz'ρ) hρfC
        have hr'b : r' < psi s ρ f := psi_closed s ρ f r' hr'f hr'ρ
        have hz'b : z' < psi s ρ f := psi_closed s ρ f z' hz'f hz'ρ
        have hρx : ρ < psi s π e :=
          psi_closed s π e ρ (C_mono_seed s e σ _ (Or.inl hσx) ρ hρC) hρπ
        rw [hρI] at hρx
        exact Ilem r' z' (by rw [← hρI]; exact le_trans hσb (Or.inl hbρ)) hρx
          (hsmall r' hr'b hr'C) (hsmall z' hz'b hz'C)
      · exfalso
        rw [hρπ] at hσb
        rcases he with h0 | ⟨e', he'⟩
        · rw [h0] at hfe
          exact not_lt_zero _ hfe
        · have hfe' : f ≤ e' := by
            rw [he'] at hfe
            exact (lt_succ_iff_le _ _).mp hfe
          obtain ⟨hpY, hpx⟩ := hpred e' he'
          have hpσ := hσY _ hpY hpx
          exact (not_lt_iff_le _ _).mpr hσb (lt_of_le_of_lt (psi_mono s π f e' hfe') hpσ)
      · exfalso
        have hlamb : lam < psi s ρ f := lt_of_lt_of_le (hσY lam hlamY hlamx) hσb
        have hzetab : zeta < psi s ρ f := lt_of_lt_of_le (hσY zeta hzetaY hzetax) hσb
        have hπC' : C s f (psi s ρ f) (I s lam zeta) :=
          C_index s f _ lam zeta (C_seed s f _ lam hlamb) (C_seed s f _ zeta hzetab)
        have hπb : I s lam zeta < psi s ρ f :=
          psi_closed s ρ f _ hπC' (by rw [← hπI]; exact hπρ)
        rw [← hπI] at hπb
        exact lt_asymm hbπ hπb
  -- Step B: the bound for the rank
  obtain ⟨wl, hwl, hwlb, hwlZ⟩ := ih k A y hk hlamY hlamiso hyA
  -- Step C: the remaining parameters
  have hJ : ∃ J, (∀ z', zeta = succ z' → I s lam z' ≤ J) ∧ J < psi s π e ∧
      ∀ A' B', C s A' B' lam → C s A' B' zeta → C s A' B' J := by
    rcases hzcases with hz0 | ⟨z', hz'⟩
    · refine ⟨0, fun z' hz' => ?_, lt_of_le_of_lt (zero_le _) hBx,
        fun _ _ _ _ => C_zero s _ _⟩
      rw [hz0] at hz'
      exact False.elim (not_lt_zero z' (by rw [hz']; exact lt_succ_self z'))
    · refine ⟨I s lam z', fun z'' hz'' => ?_, ?_, fun A' B' hl hz => ?_⟩
      · rw [hz'] at hz''
        rw [succ_injective hz'']
        exact le_refl _
      · have hz'x : z' < psi s π e := by
          apply lt_trans _ _ _ _ hzetax
          rw [hz']
          exact lt_succ_self z'
        have htπ : I s lam z' < π := by
          rw [hπI, hz']
          exact I_strict s lam (lt_succ_self z')
        exact psi_closed s π e _
          (C_index s e _ lam z' (C_seed s e _ lam hlamx) (C_seed s e _ z' hz'x)) htπ
      · have hz2 : C s A' B' (succ z') := by rw [← hz']; exact hz
        exact C_index s A' B' lam z' hl (C_predecessor s A' B' z' hz2)
  have hP : ∃ P, (∀ e', e = succ e' → psi s π e' ≤ P) ∧ P < psi s π e ∧
      ∀ A' B', C s A' B' π → C s A' B' e → e < A' → C s A' B' P := by
    rcases he with he0 | ⟨e', he'⟩
    · refine ⟨0, fun e' he' => ?_, lt_of_le_of_lt (zero_le _) hBx,
        fun _ _ _ _ _ => C_zero s _ _⟩
      rw [he0] at he'
      exact False.elim (not_lt_zero e' (by rw [he']; exact lt_succ_self e'))
    · refine ⟨psi s π e', fun e'' he'' => ?_, (hpred e' he').2, fun A' B' hπZ heZ heA' => ?_⟩
      · rw [he'] at he''
        rw [succ_injective he'']
        exact le_refl _
      · have heZ' : C s A' B' (succ e') := by rw [← he']; exact heZ
        have he'e : e' < e := by rw [he']; exact lt_succ_self e'
        exact C_collapse s A' B' π e' (lt_trans _ _ _ he'e heA') hp.1 hπZ
          (C_predecessor s A' B' e' heZ')
  obtain ⟨J, hJle, hJx, hJZ⟩ := hJ
  obtain ⟨P, hPle, hPx, hPZ⟩ := hP
  obtain ⟨L, hL⟩ : ∃ L, L = lam + zeta + J + P + psi s k y := ⟨_, rfl⟩
  have hkyx : psi s k y < psi s π e := lt_of_le_of_lt (psi_mono s k y A (Or.inl hyA)) hBx
  have hLx : L < psi s π e := by
    rw [hL]
    exact hxprin _ _ (hxprin _ _ (hxprin _ _ (hxprin _ _ hlamx hzetax) hJx) hPx) hkyx
  have hlamL : lam ≤ L := by
    rw [hL]
    exact le_trans (le_trans (le_trans (le_add _ _) (le_add _ _)) (le_add _ _)) (le_add _ _)
  have hzetaL : zeta ≤ L := by
    rw [hL]
    exact le_trans (le_trans (le_trans (right_le_add _ _) (le_add _ _)) (le_add _ _)) (le_add _ _)
  have hJL : J ≤ L := by
    rw [hL]
    exact le_trans (le_trans (right_le_add _ _) (le_add _ _)) (le_add _ _)
  have hPL : P ≤ L := by
    rw [hL]
    exact le_trans (right_le_add _ _) (le_add _ _)
  have hkyL : psi s k y ≤ L := by
    rw [hL]
    exact right_le_add _ _
  -- the bound
  have hsL : succ L < psi s π e := by
    rcases (succ_le_iff_lt _ _).mpr hLx with h | h
    · exact h
    · exact False.elim (hxlim.2 ⟨L, h.symm⟩)
  have hwlx : wl < psi s π e := lt_trans _ _ _ hwl hlamx
  have hwπ : I s wl (succ L) < π := by
    rw [hπI, ← I_rank_fixed s wl lam zeta hwl]
    apply I_strict s wl
    rw [← hπI]
    exact lt_trans _ _ _ hsL hxπ
  have hwx : I s wl (succ L) < psi s π e :=
    psi_closed s π e _ (C_index s e _ wl (succ L) (C_seed s e _ wl hwlx) (C_seed s e _ _ hsL)) hwπ
  have hLw : L < I s wl (succ L) := lt_of_lt_of_le (lt_succ_self L) (index_le_I s wl (succ L))
  refine ⟨I s wl (succ L), hwx, ?_, ?_⟩
  · -- every element of the stage closure below x lies below the bound
    intro b
    induction b using lt_wellFounded.induction with
    | h b ihb =>
      intro hb hbx
      apply lt_of_not_ge'
      intro hwb
      have hbπ : b < I s lam zeta := by rw [← hπI]; exact lt_trans _ _ _ hbx hxπ
      rcases C_canonical s y _ b hb with h0 | hseed | ⟨u, v, rfl, hub, hvb, huC, hvC⟩ |
          ⟨b1, b2, rfl, hb1, hb2, hb1C, hb2C⟩ | ⟨ρ, f, rfl, _, hρf, hρC, _⟩
      · rw [h0] at hwb
        exact (not_lt_iff_le _ _).mpr hwb (I_pos s _ _)
      · exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hseed (lt_of_le_of_lt hkyL hLw))
      · exact (not_lt_iff_le _ _).mpr hwb (I_addPrincipal s _ _ u v
          (ihb u hub huC (lt_trans _ _ _ hub hbx)) (ihb v hvb hvC (lt_trans _ _ _ hvb hbx)))
      · have hb2w := ihb b2 hb2 hb2C (lt_trans _ _ _ hb2 hbx)
        rcases I_lt_cases s b1 b2 lam zeta hbπ with ⟨hb1l, _⟩ | ⟨hb1l, hb2z⟩ | ⟨_, hIz⟩
        · have hb1wl := hwlb b1 hb1C hb1l
          have hIw : I s b1 b2 < I s wl (succ L) := by
            rw [← I_rank_fixed s b1 wl (succ L) hb1wl]
            exact I_strict s b1 hb2w
          exact (not_lt_iff_le _ _).mpr hwb hIw
        · rw [hb1l] at hwb
          rcases hzcases with hz0 | ⟨z', hz'⟩
          · rw [hz0] at hb2z
            exact not_lt_zero _ hb2z
          · have hb2z' : b2 ≤ z' := by
              rw [hz'] at hb2z
              exact (lt_succ_iff_le _ _).mp hb2z
            exact (not_lt_iff_le _ _).mpr hwb
              (lt_of_le_of_lt (le_trans (I_mono s lam hb2z') (le_trans (hJle z' hz') hJL)) hLw)
        · exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hIz (lt_of_le_of_lt hzetaL hLw))
      · have hρreg := regularIndex_regular s ρ hρf.1
        have hbρ : psi s ρ f < ρ := psi_lt s ρ f hρreg
        rcases lt_total ρ π with hρπ | hρπ | hπρ
        · have hkb : psi s k y ≤ ρ :=
            le_trans (le_trans hkyL (Or.inl hLw)) (le_trans hwb (Or.inl hbρ))
          obtain ⟨r', z', hρI, hr'ρ, hz'ρ, hr'C, hz'C⟩ :=
            C_regular_normal_presentation s y _ ρ hρreg hkb hρC
          have hρfC : C s f (psi s ρ f) (I s r' z') := by rw [← hρI]; exact hρf.2.1
          obtain ⟨hr'f, hz'f⟩ := C_normal_index_parameters s f _ r' z'
            (by rw [← hρI]; exact hr'ρ) (by rw [← hρI]; exact hz'ρ) hρfC
          have hz'b : z' < psi s ρ f := psi_closed s ρ f z' hz'f hz'ρ
          have hz'w := ihb z' hz'b hz'C (lt_trans _ _ _ hz'b hbx)
          have hρπ' : I s r' z' < I s lam zeta := by rw [← hρI, ← hπI]; exact hρπ
          rcases I_lt_cases s r' z' lam zeta hρπ' with ⟨hr'l, _⟩ | ⟨hr'l, hz'z⟩ | ⟨_, hρz⟩
          · have hr'wl := hwlb r' hr'C hr'l
            have hρw : I s r' z' < I s wl (succ L) := by
              rw [← I_rank_fixed s r' wl (succ L) hr'wl]
              exact I_strict s r' hz'w
            rw [← hρI] at hρw
            exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hbρ hρw)
          · rcases hzcases with hz0 | ⟨z'', hz''⟩
            · rw [hz0] at hz'z
              exact not_lt_zero _ hz'z
            · have hz'z'' : z' ≤ z'' := by
                rw [hz''] at hz'z
                exact (lt_succ_iff_le _ _).mp hz'z
              have hρle : ρ ≤ L := by
                rw [hρI, hr'l]
                exact le_trans (I_mono s lam hz'z'') (le_trans (hJle z'' hz'') hJL)
              exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hbρ (lt_of_le_of_lt hρle hLw))
          · rw [← hρI] at hρz
            exact (not_lt_iff_le _ _).mpr hwb
              (lt_trans _ _ _ hbρ (lt_trans _ _ _ hρz (lt_of_le_of_lt hzetaL hLw)))
        · rw [hρπ] at hwb hbx
          have hfe : f < e := by
            apply lt_of_not_ge'
            intro hef
            exact (not_lt_iff_le _ _).mpr (psi_mono s π e f hef) hbx
          rcases he with he0 | ⟨e', he'⟩
          · rw [he0] at hfe
            exact not_lt_zero _ hfe
          · have hfe' : f ≤ e' := by
              rw [he'] at hfe
              exact (lt_succ_iff_le _ _).mp hfe
            exact (not_lt_iff_le _ _).mpr hwb
              (lt_of_le_of_lt (le_trans (psi_mono s π f e' hfe') (le_trans (hPle e' he') hPL)) hLw)
        · have hlamb : lam < psi s ρ f := lt_of_lt_of_le (lt_of_le_of_lt hlamL hLw) hwb
          have hzetab : zeta < psi s ρ f := lt_of_lt_of_le (lt_of_le_of_lt hzetaL hLw) hwb
          have hπC' : C s f (psi s ρ f) (I s lam zeta) :=
            C_index s f _ lam zeta (C_seed s f _ lam hlamb) (C_seed s f _ zeta hzetab)
          have hπb : I s lam zeta < psi s ρ f :=
            psi_closed s ρ f _ hπC' (by rw [← hπI]; exact hπρ)
          exact lt_asymm hbπ hπb
  · -- uniformity
    intro A' B' hxZ hyZ hkZ hyA'
    by_cases hxB : psi s π e < B'
    · exact C_seed s A' B' _ (lt_trans _ _ _ hwx hxB)
    · have hBx' : B' ≤ psi s π e := (not_lt_iff_le _ _).mp hxB
      obtain ⟨heA', hπZ, heZ⟩ := C_proper_collapse_parameters s π e A' B' hp hBx' hxZ
      have hπZ' : C s A' B' (I s lam zeta) := by rw [← hπI]; exact hπZ
      obtain ⟨hlamZ, hzetaZ⟩ := C_normal_index_parameters s A' B' lam zeta hlaml hzetal hπZ'
      have hwlZ' := hwlZ A' B' hlamZ hyZ hkZ hyA'
      have hkyZ : C s A' B' (psi s k y) := C_collapse s A' B' k y hyA' hk hkZ hyZ
      have hLZ : C s A' B' L := by
        rw [hL]
        exact C_add s A' B' _ _ (C_add s A' B' _ _ (C_add s A' B' _ _
          (C_add s A' B' _ _ hlamZ hzetaZ) (hJZ A' B' hlamZ hzetaZ)) (hPZ A' B' hπZ heZ heA')) hkyZ
      have hA'0 : 0 < A' := lt_of_le_of_lt (zero_le y) hyA'
      exact C_index s A' B' wl (succ L) hwlZ' (C_succ s A' B' L hA'0 hLZ)

end
end OCF.Denis
