import Multi.term3.Denis.PlateauGap

/-! Reduction of `ProperClosureComplete` to a single argument-ceiling step.

By induction on the cutoff and on closure derivations, completeness reduces
to closing `PC` under one arbitrary collapse. The index and argument of the
proper presentation of that collapse are the least elements of
`C(b, psi k b)` above the collapse value and above `b`. The index is
recovered with the gap lemma; the argument is the explicit proposition
`ArgumentCeilingStep`, which is not assumed. -/

namespace OCF.Denis
open Ordinal
noncomputable section

/-- Every closure element lies below an element of any closure whose seed
contains the original seed. -/
theorem C_has_ceiling (s : Supply) (a beta c gamma : O) (hbg : beta ≤ gamma)
    (y : O) (hy : C s a beta y) : ∃ d, C s c gamma d ∧ y ≤ d := by
  apply C_least s a beta (fun y => ∃ d, C s c gamma d ∧ y ≤ d) _ _ _ _ _ y hy
  · exact ⟨0, C_zero s c gamma, le_refl _⟩
  · intro x hx
    exact ⟨x, C_seed s c gamma x (lt_of_lt_of_le hx hbg), le_refl x⟩
  · rintro x y ⟨d1, hd1, hx⟩ ⟨d2, hd2, hy⟩
    exact ⟨d1 + d2, C_add s c gamma d1 d2 hd1 hd2,
      le_trans (add_mono_left hx y) (add_mono_right d1 hy)⟩
  · rintro x y ⟨d1, hd1, hx⟩ ⟨d2, hd2, hy⟩
    exact ⟨I s d1 d2, C_index s c gamma d1 d2 hd1 hd2, I_mono_both s hx hy⟩
  · rintro k b _ hk ⟨d1, hd1, hkd⟩ _
    exact ⟨d1, hd1, Or.inl (lt_of_lt_of_le (psi_lt s k b (regularIndex_regular s k hk)) hkd)⟩

/-- Completeness for all cutoffs below `a`. -/
def CompleteBelow (s : Supply) (a : O) : Prop :=
  ∀ a', a' < a → ∀ beta x, C s a' beta x → PC s a' beta x

/-- Closure of `PC` under one arbitrary collapse, given completeness below
the cutoff. -/
def PCCollapseStep (s : Supply) : Prop :=
  ∀ a beta k b, CompleteBelow s a → RegularIndex s k → PC s a beta k → PC s a beta b →
    b < a → PC s a beta (psi s k b)

theorem properClosureComplete_of_collapse_step (s : Supply) (h : PCCollapseStep s) :
    ProperClosureComplete s := by
  intro a
  induction a using lt_wellFounded.induction with
  | h a ih =>
    intro beta x hx
    exact C_least s a beta (PC s a beta) .zero (fun x hx => .seed hx)
      (fun _ _ hx hy => .add hx hy) (fun _ _ hx hy => .index hx hy)
      (fun k b hb hk hkP hbP => h a beta k b (fun a' ha' => ih a' ha') hk hkP hbP hb) x hx

/-- The least element `bstar ≥ b` of the defining closure is the top of
the argument plateau: the closure is unchanged up to `bstar`, and so is
the collapse value. -/
theorem plateau_top (s : Supply) (k b bstar : O) (hb : b ≤ bstar)
    (hleast : ∀ d, C s b (psi s k b) d → b ≤ d → bstar ≤ d) :
    (∀ xi, xi ≤ psi s k b → ∀ x, C s bstar xi x → C s b xi x) ∧
      psi s k bstar = psi s k b := by
  have hres : ∀ xi, xi ≤ psi s k b → ∀ x, C s bstar xi x → C s b xi x := by
    intro xi hxi x hx
    apply C_least s bstar xi (C s b xi) (C_zero s b xi) (C_seed s b xi) (C_add s b xi)
      (C_index s b xi) _ x hx
    intro l e he hl hlC heC
    apply C_collapse s b xi l e _ hl hlC heC
    apply lt_of_not_ge'
    intro hbe
    exact (not_lt_iff_le _ _).mpr (hleast e (C_mono_seed s b xi _ hxi e heC) hbe) he
  refine ⟨hres, le_antisymm ?_ (psi_mono s k b bstar hb)⟩
  apply psi_min s k bstar (psi s k b)
  exact ⟨psi_le s k b, fun x hx hxk => psi_closed s k b x (hres _ (le_refl _) x hx) hxk⟩

/-- The least element of the defining closure above the collapse value is
a regular index generated below the value, lies above the original index,
and gives the same collapse. -/
theorem index_ceiling (s : Supply) (k b kstar : O) (hk : RegularIndex s k)
    (hks : C s b (psi s k b) kstar) (hge : psi s k b ≤ kstar)
    (hleast : ∀ d, C s b (psi s k b) d → psi s k b ≤ d → kstar ≤ d) :
    k ≤ kstar ∧ RegularIndex s kstar ∧ psi s kstar b = psi s k b ∧
      ∃ r z, kstar = I s r z ∧ r < psi s k b ∧ z < psi s k b := by
  classical
  have hreg := regularIndex_regular s k hk
  have hlt : psi s k b < k := psi_lt s k b hreg
  have hgap : ∀ d, C s b (psi s k b) d → d < kstar → d < psi s k b := by
    intro d hd hdk
    apply lt_of_not_ge'
    intro hgd
    exact (not_lt_iff_le _ _).mpr (hleast d hd hgd) hdk
  have hkk : k ≤ kstar := by
    apply (not_lt_iff_le _ _).mp
    intro hkl
    exact (not_lt_iff_le _ _).mpr hge (psi_closed s k b kstar hks hkl)
  have hne : psi s k b < kstar := by
    rcases hge with h | h
    · exact h
    · exact False.elim (lt_irrefl _ (psi_closed s k b _ (h ▸ hks) hlt))
  have hprin := psi_addPrincipal s k b hreg
  -- the normal presentation of `kstar` comes from below the collapse value
  have aux (y : O) (hy : StageClosure s b (fun c _ => stages s c) (psi s k b) y) :
      y = kstar → ∃ r z, kstar = I s r z ∧ r < psi s k b ∧ z < psi s k b := by
    induction hy with
    | zero =>
      intro h
      exact False.elim (not_lt_zero _ (h ▸ hne))
    | seed hy =>
      intro h
      exact False.elim (lt_asymm hne (h ▸ hy))
    | @add u v hu hv ihu ihv =>
      intro h
      rcases le_add u v with hu' | hu'
      · rcases right_le_add u v with hv' | hv'
        · rw [h] at hu' hv'
          have hu'' := hgap u ((C_iff s b _ u).mpr hu) hu'
          have hv'' := hgap v ((C_iff s b _ v).mpr hv) hv'
          exact False.elim (lt_asymm hne (h ▸ hprin u v hu'' hv''))
        · exact ihv (hv'.trans h)
      · exact ihu (hu'.trans h)
    | @index u v hu hv ihu ihv =>
      intro h
      rcases rank_le_I s u v with hu' | hu'
      · rcases index_le_I s u v with hv' | hv'
        · rw [h] at hu' hv'
          exact ⟨u, v, h.symm, hgap u ((C_iff s b _ u).mpr hu) hu',
            hgap v ((C_iff s b _ v).mpr hv) hv'⟩
        · exact ihv (hv'.trans h)
      · exact ihu (hu'.trans h)
    | @collapse l e he hl hlC heC ihl ihe =>
      intro h
      change psi s l e = kstar at h
      have hlreg := regularIndex_regular s l hl
      have hex : ∃ x, C s e (psi s k b) x ∧ x < l ∧ psi s k b ≤ x := by
        apply Classical.byContradiction
        intro hnot
        have hle : psi s l e ≤ psi s k b := by
          apply psi_min s l e (psi s k b)
          refine ⟨Or.inl (lt_trans _ _ _ (h ▸ hne) (psi_lt s l e hlreg)), ?_⟩
          intro x hx hxl
          apply lt_of_not_ge'
          intro hgx
          exact hnot ⟨x, hx, hxl, hgx⟩
        exact (not_lt_iff_le _ _).mpr hle (h ▸ hne)
      obtain ⟨x, hx, hxl, hgx⟩ := hex
      have hxD : C s b (psi s k b) x := C_mono_argument s e b _ (Or.inl he) x hx
      have hxk : x < kstar := h ▸ psi_closed s l e x
        (C_mono_seed s e _ _ (h ▸ hge) x hx) hxl
      exact False.elim ((not_lt_iff_le _ _).mpr hgx (hgap x hxD hxk))
  obtain ⟨r, z, hI, hr, hz⟩ := aux kstar ((C_iff s b _ kstar).mp hks) rfl
  have hRI : RegularIndex s kstar := by
    by_cases hz0 : z = 0
    · exact Or.inl ⟨r, hz0 ▸ hI⟩
    · by_cases hzs : ∃ c, z = succ c
      · obtain ⟨c, hc⟩ := hzs
        exact Or.inr ⟨r, c, hc ▸ hI⟩
      · have hlim : IsLimit z := ⟨hz0, hzs⟩
        have hle : I s r z ≤ psi s k b := by
          apply I_limit_le_of_forall s r z _ hlim
          intro c hc
          have hcD : C s b (psi s k b) (I s r c) :=
            C_index s b _ r c (C_seed s b _ r hr) (C_seed s b _ c (lt_trans _ _ _ hc hz))
          exact Or.inl (hgap _ hcD (hI ▸ I_strict s r hc))
        exact False.elim ((not_lt_iff_le _ _).mpr (hI ▸ hle) hne)
  refine ⟨hkk, hRI, le_antisymm ?_ (psi_mono_index s k kstar b hkk), r, z, hI, hr, hz⟩
  exact psi_min s kstar b (psi s k b) ⟨Or.inl hne, fun x hx hxk => hgap x hx hxk⟩

/-- The gap lemma for the Jäger-style closure. -/
theorem PC_index_gap (s : Supply) (a beta gamma G r0 z0 : O)
    (hprin : AddPrincipal gamma) (hbeta : beta ≤ gamma)
    (hG : G = I s r0 z0) (hr0 : r0 < gamma) (hz0 : z0 < gamma)
    (hgap : ∀ r z, r < gamma → z < gamma → I s r z < G → I s r z < gamma)
    (y : O) (hy : PC s a beta y) (hlo : gamma ≤ y) (hhi : y < G) : PC s a beta G := by
  induction hy with
  | zero => exact False.elim (not_lt_zero r0 (lt_of_lt_of_le hr0 hlo))
  | seed hy => exact False.elim (lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le hy hbeta) hlo))
  | @add u w hu hw ihu ihw =>
    by_cases hu' : gamma ≤ u
    · exact ihu hu' (lt_of_le_of_lt (le_add u w) hhi)
    · by_cases hw' : gamma ≤ w
      · exact ihw hw' (lt_of_le_of_lt (right_le_add u w) hhi)
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo
          (hprin u w (lt_of_not_ge' hu') (lt_of_not_ge' hw'))))
  | @index u w hu hw ihu ihw =>
    by_cases hu' : gamma ≤ u
    · exact ihu hu' (lt_of_le_of_lt (rank_le_I s u w) hhi)
    · by_cases hw' : gamma ≤ w
      · exact ihw hw' (lt_of_le_of_lt (index_le_I s u w) hhi)
      · exact False.elim (lt_irrefl _ (lt_of_le_of_lt hlo
          (hgap u w (lt_of_not_ge' hu') (lt_of_not_ge' hw') hhi)))
  | @collapse k b hb hp hkc hbc ihk ihb =>
    have hreg := regularIndex_regular s k hp.1
    rcases lt_total k G with hkG | hkG | hGk
    · exact ihk (le_trans hlo (Or.inl (psi_lt s k b hreg))) hkG
    · exact hkG ▸ hkc
    · have hmem : C s b (psi s k b) G := by
        rw [hG]
        exact C_index s b _ r0 z0 (C_seed s b _ r0 (lt_of_lt_of_le hr0 hlo))
          (C_seed s b _ z0 (lt_of_lt_of_le hz0 hlo))
      exact False.elim (lt_asymm hhi (psi_closed s k b G hmem hGk))

/-- The remaining step: the least element of the defining closure above the
argument of an arbitrary collapse is again in the Jäger-style closure.
This is an explicit proposition, not an axiom. -/
def ArgumentCeilingStep (s : Supply) : Prop :=
  ∀ a beta k b bstar, CompleteBelow s a → RegularIndex s k → PC s a beta k →
    PC s a beta b → b < a → beta ≤ psi s k b → C s b (psi s k b) bstar → b ≤ bstar →
    (∀ d, C s b (psi s k b) d → b ≤ d → bstar ≤ d) → PC s a beta bstar

/-- One collapse is closed in `PC` as soon as its argument ceiling is. -/
theorem collapse_closed_of_ceiling (s : Supply) (a beta k b : O)
    (hk : RegularIndex s k) (hkP : PC s a beta k) (hbP : PC s a beta b) (hba : b < a)
    (hceil : beta ≤ psi s k b → ∀ bstar, C s b (psi s k b) bstar → b ≤ bstar →
      (∀ d, C s b (psi s k b) d → b ≤ d → bstar ≤ d) → PC s a beta bstar) :
    PC s a beta (psi s k b) := by
  by_cases hsmall : psi s k b < beta
  · exact .seed hsmall
  have hbg : beta ≤ psi s k b := (not_lt_iff_le _ _).mp hsmall
  have hreg := regularIndex_regular s k hk
  have hexb := C_has_ceiling s a beta b (psi s k b) hbg b hbP.sub_C
  have hbs := (least_spec _ hexb).1
  have hbleast : ∀ d, C s b (psi s k b) d → b ≤ d →
      least (fun d => C s b (psi s k b) d ∧ b ≤ d) hexb ≤ d :=
    fun d hd hbd => least_le _ hexb ⟨hd, hbd⟩
  obtain ⟨dk, hdk, hkd⟩ := C_has_ceiling s a beta b (psi s k b) hbg k hkP.sub_C
  have hexk : ∃ d, C s b (psi s k b) d ∧ psi s k b ≤ d :=
    ⟨dk, hdk, le_trans (Or.inl (psi_lt s k b hreg)) hkd⟩
  have hks := (least_spec _ hexk).1
  have hkleast : ∀ d, C s b (psi s k b) d → psi s k b ≤ d →
      least (fun d => C s b (psi s k b) d ∧ psi s k b ≤ d) hexk ≤ d :=
    fun d hd hgd => least_le _ hexk ⟨hd, hgd⟩
  generalize least (fun d => C s b (psi s k b) d ∧ b ≤ d) hexb = bstar at hbs hbleast
  generalize least (fun d => C s b (psi s k b) d ∧ psi s k b ≤ d) hexk = kstar at hks hkleast
  obtain ⟨hres, hpsib⟩ := plateau_top s k b bstar hbs.2 hbleast
  obtain ⟨hkk, hRI, hpsik, r0, z0, hI, hr0, hz0⟩ :=
    index_ceiling s k b kstar hk hks.1 hks.2 hkleast
  have hval : psi s kstar bstar = psi s k b := by
    apply le_antisymm
    · apply psi_min s kstar bstar (psi s k b)
      refine ⟨hks.2, fun x hx hxk => ?_⟩
      apply lt_of_not_ge'
      intro hgx
      exact (not_lt_iff_le _ _).mpr (hkleast x (hres _ (le_refl _) x hx) hgx) hxk
    · rw [← hpsik]
      exact psi_mono s kstar b bstar hbs.2
  have hproper : ProperCollapse s kstar bstar := by
    refine ⟨hRI, ?_, ?_⟩
    · rw [hval]
      exact C_mono_argument s b bstar _ hbs.2 kstar hks.1
    · rw [hval]
      exact C_mono_argument s b bstar _ hbs.2 bstar hbs.1
  have hkstarP : PC s a beta kstar := by
    rcases hkk with hlt | heq
    · apply PC_index_gap s a beta (psi s k b) kstar r0 z0 (psi_addPrincipal s k b hreg)
        hbg hI hr0 hz0 _ k hkP (Or.inl (psi_lt s k b hreg)) hlt
      intro r z hr hz hrz
      apply lt_of_not_ge'
      intro hgz
      exact (not_lt_iff_le _ _).mpr
        (hkleast _ (C_index s b _ r z (C_seed s b _ r hr) (C_seed s b _ z hz)) hgz) hrz
    · exact heq ▸ hkP
  have hbstarP := hceil hbg bstar hbs.1 hbs.2 hbleast
  have hxC : C s a beta (psi s kstar bstar) := by
    rw [hval]
    exact C_collapse s a beta k b hba hk hkP.sub_C hbP.sub_C
  have hbg' : beta ≤ psi s kstar bstar := by
    rw [hval]
    exact hbg
  have hba' := C_collapse_argument_lt s a beta kstar bstar hRI hbg' hxC
  have hresult := PC.collapse hba' hproper hkstarP hbstarP
  rw [hval] at hresult
  exact hresult

theorem pcCollapseStep_of_argumentCeiling (s : Supply) (h : ArgumentCeilingStep s) :
    PCCollapseStep s := by
  intro a beta k b hbelow hk hkP hbP hba
  exact collapse_closed_of_ceiling s a beta k b hk hkP hbP hba
    (fun hbg bstar h1 h2 h3 => h a beta k b bstar hbelow hk hkP hbP hba hbg h1 h2 h3)

/-- Completeness of the Jäger-style closure, hence general argument
recovery, follows from the argument-ceiling step alone. -/
theorem properClosureComplete_of_argumentCeiling (s : Supply) (h : ArgumentCeilingStep s) :
    ProperClosureComplete s :=
  properClosureComplete_of_collapse_step s (pcCollapseStep_of_argumentCeiling s h)

end
end OCF.Denis
