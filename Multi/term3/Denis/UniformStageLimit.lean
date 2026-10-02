import Multi.term3.Denis.UniformStage

/-! The uniform stage bound at a proper collapse with a limit argument.

Let `x = psi π e` be isolated in `Y = C(A, psi k A)`, with `(π, e)` proper
and `e` a limit.

1. No smaller argument has the same value. Otherwise `e` is isolated in its
   own closure `C(e, x)`, and iterating the uniform bound for `e` there
   produces collapse values in `Y`, all below `x` and cofinal in `x`.
2. Hence `e` is isolated in `Y`, and the bound `We` for `e` exists.
3. The bound for `x` is the least collapse `psi π f` (with `f` from
   `C(e, x)`) above the parameters of `π`, the stage seed and `psi π We`.
   A least counterexample in the stage closure is impossible: sums and `I`
   values stay below a collapse value, a collapse at a smaller index has
   its index below the bound, one at the same index has its argument below
   `We`, and one at a larger index would generate `π` below itself. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem ustage_psi_limit (s : Supply) (π e rπ zπ : O) (hp : ProperCollapse s π e)
    (he : IsLimit e) (hπI : π = I s rπ zπ) (hrπ : rπ < π) (hzπ : zπ < π)
    (ih : UStage s e) : UStage s (psi s π e) := by
  intro k A y hk hxY hiso hyA
  have hπreg := regularIndex_regular s π hp.1
  have hxπ : psi s π e < π := psi_lt s π e hπreg
  have hBx : psi s k A < psi s π e := hiso.seed_lt
  obtain ⟨heA, hπY, heY⟩ := C_proper_collapse_parameters s π e A _ hp (Or.inl hBx) hxY
  have hrπl : rπ < I s rπ zπ := by rw [← hπI]; exact hrπ
  have hzπl : zπ < I s rπ zπ := by rw [← hπI]; exact hzπ
  have hπC : C s e (psi s π e) (I s rπ zπ) := by rw [← hπI]; exact hp.2.1
  obtain ⟨hrπC, hzπC⟩ := C_normal_index_parameters s e _ rπ zπ hrπl hzπl hπC
  have hrπx : rπ < psi s π e := psi_closed s π e rπ hrπC hrπ
  have hzπx : zπ < psi s π e := psi_closed s π e zπ hzπC hzπ
  have he0 : 0 < e := (zero_lt_iff_ne_zero e).mpr he.1
  -- Step 1: no smaller argument has the same value
  have hlt : ∀ d, d < e → psi s π d < psi s π e := by
    classical
    have hex : ∃ d, psi s π d = psi s π e := ⟨e, rfl⟩
    have hspec := least_spec _ hex
    have he1e : least (fun d => psi s π d = psi s π e) hex ≤ e := least_le _ hex rfl
    generalize least (fun d => psi s π d = psi s π e) hex = e1 at hspec he1e
    have he1 : e1 = e := by
      rcases he1e with he1lt | he1eq
      · exfalso
        obtain ⟨_, _, hgap⟩ := psi_proper_plateau s π e π e1 hp.1 hp.1 hp.2.1 hp.2.2 hspec.1
        have hiso' : IsoIn s e (psi s π e) e := ⟨he, e1, he1lt, hgap⟩
        let P : O → Prop := fun z => C s e (psi s π e) z ∧ C s A (psi s k A) z
        have hnext : ∀ z, P z → z < e → ∃ z', P z' ∧ z' < e ∧ z ≤ z' ∧
            ∀ b, C s z (psi s π z) b → b < e → b < z' := by
          intro z hz hze
          obtain ⟨w, hwe, hwb, hwZ⟩ := ih π e z hp.1 hp.2.2 hiso' hze
          have hwP : P w := ⟨hwZ e _ hp.2.2 hz.1 hp.2.1 hze,
            hwZ A _ heY hz.2 hπY (lt_trans _ _ _ hze heA)⟩
          refine ⟨omax z w, ?_, ?_, le_omax_left z w, fun b hb hbe =>
            lt_of_lt_of_le (hwb b hb hbe) (le_omax_right z w)⟩
          · rcases omax_cases z w with h | h <;> rw [h]
            · exact hz
            · exact hwP
          · rcases omax_cases z w with h | h <;> rw [h]
            · exact hze
            · exact hwe
        obtain ⟨xs, hxs, hsup⟩ :=
          stage_iteration s π e P ⟨C_zero s _ _, C_zero s _ _⟩ he0 hnext
        obtain ⟨_, c, hcx, hc⟩ := hiso
        obtain ⟨n, hn⟩ := (lt_sup_iff _ c).mp (lt_of_lt_of_le hcx hsup)
        have hxn1 : xs n < e1 := by
          apply lt_of_not_ge'
          intro h
          exact hgap (xs n) (hxs n).1.1 h (hxs n).2
        have hne : psi s π (xs n) ≠ psi s π e := hspec.2 (xs n) hxn1
        have hlt' : psi s π (xs n) < psi s π e := by
          rcases psi_mono s π _ _ (Or.inl (hxs n).2) with h | h
          · exact h
          · exact absurd h hne
        exact hc (psi s π (xs n)) (C_collapse s A _ π (xs n)
          (lt_trans _ _ _ (hxs n).2 heA) hp.1 hπY (hxs n).1.2) (Or.inl hn) hlt'
      · exact he1eq
    intro d hd
    have hd1 : d < e1 := by rw [he1]; exact hd
    rcases psi_mono s π d e (Or.inl hd) with h | h
    · exact h
    · exact absurd h (hspec.2 d hd1)
  -- Step 2: the argument is isolated
  have heiso : IsoIn s A (psi s k A) e := by
    obtain ⟨_, c, hcx, hc⟩ := hiso
    obtain ⟨e0, he0e, hce0⟩ := psi_limit_cofinal' s π e c he hcx
    refine ⟨he, e0, he0e, fun d hd he0d hde => ?_⟩
    exact hc (psi s π d) (C_collapse s A _ π d (lt_trans _ _ _ hde heA) hp.1 hπY hd)
      (le_trans (Or.inl hce0) (psi_mono s π e0 d he0d)) (hlt d hde)
  -- Step 3: the bound for the argument
  obtain ⟨We, hWe, hWeb, hWeZ⟩ := ih k A y hk heY heiso hyA
  -- Step 4: the separation value above the parameters
  have hxprin := psi_addPrincipal s π e hπreg
  have hkyx : psi s k y < psi s π e := lt_of_le_of_lt (psi_mono s k y A (Or.inl hyA)) hBx
  have hWex : psi s π We < psi s π e := hlt We hWe
  obtain ⟨m, hm⟩ : ∃ m, m = rπ + zπ + psi s k y + psi s π We := ⟨_, rfl⟩
  have hmx : m < psi s π e := by
    rw [hm]
    exact hxprin _ _ (hxprin _ _ (hxprin _ _ hrπx hzπx) hkyx) hWex
  have hrπm : rπ ≤ m := by
    rw [hm]
    exact le_trans (le_trans (le_add rπ zπ) (le_add _ _)) (le_add _ _)
  have hzπm : zπ ≤ m := by
    rw [hm]
    exact le_trans (le_trans (right_le_add rπ zπ) (le_add _ _)) (le_add _ _)
  have hkym : psi s k y ≤ m := by
    rw [hm]
    exact le_trans (right_le_add _ _) (le_add _ _)
  have hWem : psi s π We ≤ m := by
    rw [hm]
    exact right_le_add _ _
  have hexd : ∃ d, m < psi s π d := ⟨e, hmx⟩
  have hdspec := least_spec _ hexd
  have hdle : least (fun d => m < psi s π d) hexd ≤ e := least_le _ hexd hmx
  generalize least (fun d => m < psi s π d) hexd = d1 at hdspec hdle
  have hcases := least_exceeding_argument s π m d1 hdspec.1
    (fun d' hd' => (not_lt_iff_le _ _).mp (hdspec.2 d' hd'))
  have hd1e : d1 < e := by
    rcases hdle with h | h
    · exact h
    · exfalso
      rcases hcases with h0 | ⟨d', hd', _, _⟩
      · exact he.1 (h ▸ h0)
      · exact he.2 ⟨d', h ▸ hd'⟩
  have hd1C : C s e (psi s π e) d1 := by
    rcases hcases with h0 | ⟨d', hd', _, hd'C⟩
    · rw [h0]
      exact C_zero s _ _
    · rw [hd']
      apply C_succ s e _ d' he0
      have hd'e : d' ≤ e := by
        rw [hd'] at hd1e
        exact Or.inl (lt_trans _ _ _ (lt_succ_self d') hd1e)
      exact C_mono_argument s d' e _ hd'e d'
        (C_mono_seed s d' _ _ (psi_mono s π d' e hd'e) d' hd'C)
  obtain ⟨w, hw⟩ := IsSep.exists s e (psi s π e) π m ⟨d1, hd1e, hd1C, hdspec.1⟩
  have hwsep := hw
  obtain ⟨fw, hfwe, _, hwfw, hmw, _⟩ := hw
  subst hwfw
  have hwx : psi s π fw < psi s π e := hlt fw hfwe
  refine ⟨psi s π fw, hwx, ?_, ?_⟩
  · -- every element of the stage closure below x lies below the bound
    intro b
    induction b using lt_wellFounded.induction with
    | h b ihb =>
      intro hb hbx
      apply lt_of_not_ge'
      intro hwb
      rcases C_canonical s y _ b hb with h0 | hseed | ⟨u, v, rfl, hub, hvb, huC, hvC⟩ |
          ⟨r', z', rfl, hr'b, hz'b, hr'C, hz'C⟩ | ⟨ρ, f, rfl, _, hρf, hρC, hfC⟩
      · rw [h0] at hwb
        exact (not_lt_iff_le _ _).mpr hwb (lt_of_le_of_lt (zero_le m) hmw)
      · exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hseed (lt_of_le_of_lt hkym hmw))
      · have hu := ihb u hub huC (lt_trans _ _ _ hub hbx)
        have hv := ihb v hvb hvC (lt_trans _ _ _ hvb hbx)
        exact (not_lt_iff_le _ _).mpr hwb (psi_addPrincipal s π fw hπreg u v hu hv)
      · have hr' := ihb r' hr'b hr'C (lt_trans _ _ _ hr'b hbx)
        have hz' := ihb z' hz'b hz'C (lt_trans _ _ _ hz'b hbx)
        have hIC : C s fw (psi s π fw) (I s r' z') :=
          C_index s fw _ r' z' (C_seed s fw _ r' hr') (C_seed s fw _ z' hz')
        exact (not_lt_iff_le _ _).mpr hwb (psi_closed s π fw _ hIC (lt_trans _ _ _ hbx hxπ))
      · have hρreg := regularIndex_regular s ρ hρf.1
        have hbρ : psi s ρ f < ρ := psi_lt s ρ f hρreg
        rcases lt_total ρ π with hρπ | hρπ | hπρ
        · -- a smaller index lies below the bound
          have hkb : psi s k y ≤ ρ :=
            le_trans (le_trans hkym (Or.inl hmw)) (le_trans hwb (Or.inl hbρ))
          obtain ⟨r', z', hρI, hr'ρ, hz'ρ, hr'C, hz'C⟩ :=
            C_regular_normal_presentation s y _ ρ hρreg hkb hρC
          have hρfC : C s f (psi s ρ f) (I s r' z') := by rw [← hρI]; exact hρf.2.1
          obtain ⟨hr'f, hz'f⟩ := C_normal_index_parameters s f _ r' z'
            (by rw [← hρI]; exact hr'ρ) (by rw [← hρI]; exact hz'ρ) hρfC
          have hr'b : r' < psi s ρ f := psi_closed s ρ f r' hr'f hr'ρ
          have hz'b : z' < psi s ρ f := psi_closed s ρ f z' hz'f hz'ρ
          have hr' := ihb r' hr'b hr'C (lt_trans _ _ _ hr'b hbx)
          have hz' := ihb z' hz'b hz'C (lt_trans _ _ _ hz'b hbx)
          have hIC : C s fw (psi s π fw) (I s r' z') :=
            C_index s fw _ r' z' (C_seed s fw _ r' hr') (C_seed s fw _ z' hz')
          have hρw : ρ < psi s π fw := by
            rw [hρI]
            exact psi_closed s π fw _ hIC (by rw [← hρI]; exact hρπ)
          exact (not_lt_iff_le _ _).mpr hwb (lt_trans _ _ _ hbρ hρw)
        · -- the same index: the argument lies below the bound of `e`
          rw [hρπ] at hwb hbx
          have hfe : f < e := by
            apply lt_of_not_ge'
            intro hef
            exact (not_lt_iff_le _ _).mpr (psi_mono s π e f hef) hbx
          have hfWe := hWeb f hfC hfe
          exact (not_lt_iff_le _ _).mpr hwb
            (lt_of_le_of_lt (le_trans (psi_mono s π f We (Or.inl hfWe)) hWem) hmw)
        · -- a larger index would generate `π` below the collapse value
          have hrπb : rπ < psi s ρ f := lt_of_lt_of_le (lt_of_le_of_lt hrπm hmw) hwb
          have hzπb : zπ < psi s ρ f := lt_of_lt_of_le (lt_of_le_of_lt hzπm hmw) hwb
          have hπC' : C s f (psi s ρ f) (I s rπ zπ) :=
            C_index s f _ rπ zπ (C_seed s f _ rπ hrπb) (C_seed s f _ zπ hzπb)
          have hπb : I s rπ zπ < psi s ρ f :=
            psi_closed s ρ f _ hπC' (by rw [← hπI]; exact hπρ)
          rw [← hπI] at hπb
          exact lt_asymm (lt_trans _ _ _ hbx hxπ) hπb
  · -- uniformity
    intro A' B' hxZ hyZ hkZ hyA'
    by_cases hxB : psi s π e < B'
    · exact C_seed s A' B' _ (lt_trans _ _ _ hwx hxB)
    · have hBx' : B' ≤ psi s π e := (not_lt_iff_le _ _).mp hxB
      obtain ⟨heA', hπZ, heZ⟩ := C_proper_collapse_parameters s π e A' B' hp hBx' hxZ
      have hπZ' : C s A' B' (I s rπ zπ) := by rw [← hπI]; exact hπZ
      obtain ⟨hrπZ, hzπZ⟩ := C_normal_index_parameters s A' B' rπ zπ hrπl hzπl hπZ'
      have hkyZ : C s A' B' (psi s k y) := C_collapse s A' B' k y hyA' hk hkZ hyZ
      have hWeZ' := hWeZ A' B' heZ hyZ hkZ hyA'
      have hpWZ : C s A' B' (psi s π We) :=
        C_collapse s A' B' π We (lt_trans _ _ _ hWe heA') hp.1 hπZ hWeZ'
      have hmZ : C s A' B' m := by
        rw [hm]
        exact C_add s A' B' _ _ (C_add s A' B' _ _ (C_add s A' B' _ _ hrπZ hzπZ) hkyZ) hpWZ
      exact sep_mem s A' B' e (psi s π e) π m _ he0 heA' hBx' hp.1 hp.2.1 hπZ hmZ hwsep

end
end OCF.Denis
