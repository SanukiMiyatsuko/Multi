import Multi.term3.Denis.CeilingBasics

/-! The least collapse value `psi k d` above an element, with `d` an
argument of a fixed closure, computed from the parts of the element. -/

namespace OCF.Denis
open Ordinal
noncomputable section

theorem IsSep.exists (s : Supply) (c gamma k y : O)
    (h : ∃ d, d < c ∧ C s c gamma d ∧ y < psi s k d) : ∃ t, IsSep s c gamma k y t := by
  have hspec := least_spec _ h
  generalize least (fun d => d < c ∧ C s c gamma d ∧ y < psi s k d) h = d1 at hspec
  obtain ⟨⟨hdc, hd, hyd⟩, hmin⟩ := hspec
  refine ⟨psi s k d1, d1, hdc, hd, rfl, hyd, fun d' hd'c hd' hyd' => psi_mono s k d1 d' ?_⟩
  exact (not_lt_iff_le _ _).mp (fun hlt => hmin d' hlt ⟨hd'c, hd', hyd'⟩)

theorem IsSep.le_of {s : Supply} {c gamma k y t : O} (h : IsSep s c gamma k y t)
    {d : O} (hdc : d < c) (hd : C s c gamma d) (hyd : y < psi s k d) : t ≤ psi s k d := by
  obtain ⟨_, _, _, _, _, hmin⟩ := h
  exact hmin d hdc hd hyd

theorem IsSep.lt {s : Supply} {c gamma k y t : O} (h : IsSep s c gamma k y t) : y < t := by
  obtain ⟨d, _, _, rfl, hyt, _⟩ := h
  exact hyt

/-- The separation value of a combination of two parts is that of one part,
provided collapse values above both parts lie above the combination. -/
theorem IsSep.of_parts {s : Supply} {c gamma k u v y t : O} (h : IsSep s c gamma k y t)
    (hu : u ≤ y) (hv : v ≤ y)
    (hcomb : ∀ d, u < psi s k d → v < psi s k d → y < psi s k d) :
    IsSep s c gamma k u t ∨ IsSep s c gamma k v t := by
  obtain ⟨d, hdc, hd, rfl, hyt, hmin⟩ := h
  obtain ⟨t1, h1⟩ := IsSep.exists s c gamma k u ⟨d, hdc, hd, lt_of_le_of_lt hu hyt⟩
  obtain ⟨t2, h2⟩ := IsSep.exists s c gamma k v ⟨d, hdc, hd, lt_of_le_of_lt hv hyt⟩
  obtain ⟨d1, hd1c, hd1, rfl, hu1, hmin1⟩ := h1
  obtain ⟨d2, hd2c, hd2, rfl, hv2, hmin2⟩ := h2
  have h1le : psi s k d1 ≤ psi s k d := hmin1 d hdc hd (lt_of_le_of_lt hu hyt)
  have h2le : psi s k d2 ≤ psi s k d := hmin2 d hdc hd (lt_of_le_of_lt hv hyt)
  rcases lt_total d1 d2 with h12 | h12 | h12
  · have hge := hmin d2 hd2c hd2
      (hcomb d2 (lt_of_lt_of_le hu1 (psi_mono s k d1 d2 (Or.inl h12))) hv2)
    right
    rw [← le_antisymm h2le hge]
    exact ⟨d2, hd2c, hd2, rfl, hv2, hmin2⟩
  · subst h12
    have hge := hmin d1 hd1c hd1 (hcomb d1 hu1 hv2)
    left
    rw [← le_antisymm h1le hge]
    exact ⟨d1, hd1c, hd1, rfl, hu1, hmin1⟩
  · have hge := hmin d1 hd1c hd1
      (hcomb d1 hu1 (lt_of_lt_of_le hv2 (psi_mono s k d2 d1 (Or.inl h12))))
    left
    rw [← le_antisymm h1le hge]
    exact ⟨d1, hd1c, hd1, rfl, hu1, hmin1⟩

theorem IsSep.of_add {s : Supply} {c gamma k u v t : O} (hk : RegularIndex s k)
    (h : IsSep s c gamma k (u + v) t) : IsSep s c gamma k u t ∨ IsSep s c gamma k v t :=
  h.of_parts (le_add u v) (right_le_add u v)
    (fun d hu hv => psi_addPrincipal s k d (regularIndex_regular s k hk) u v hu hv)

theorem C_succ (s : Supply) (c beta x : O) (hc : 0 < c) (hx : C s c beta x) :
    C s c beta (succ x) := by
  have h := C_add s c beta x (succ 0) hx (C_finite s c beta hc 1)
  rwa [add_succ, add_zero] at h

/-- The index of a proper collapse has a normal presentation from below
the collapse value. -/
theorem proper_index_params_below (s : Supply) (p e : O) (hp : ProperCollapse s p e) :
    ∃ r z, p = I s r z ∧ r < psi s p e ∧ z < psi s p e := by
  have hreg := regularIndex_regular s p hp.1
  obtain ⟨r, z, hI, hr, hz, hrC, hzC⟩ :=
    C_regular_normal_presentation s e (psi s p e) p hreg (psi_le s p e) hp.2.1
  exact ⟨r, z, hI, psi_closed s p e r hrC hr, psi_closed s p e z hzC hz⟩

/-- Below an index `k`, the separation value of a proper collapse with a
smaller index is that of its index. -/
theorem IsSep.of_collapse_below {s : Supply} {c gamma k p e t : O}
    (hp : ProperCollapse s p e) (hpk : p < k)
    (h : IsSep s c gamma k (psi s p e) t) : IsSep s c gamma k p t := by
  obtain ⟨d, hdc, hd, rfl, hyt, hmin⟩ := h
  obtain ⟨r, z, hI, hr, hz⟩ := proper_index_params_below s p e hp
  have hpC : C s d (psi s k d) p := by
    rw [hI]
    exact C_index s d _ r z (C_seed s d _ r (lt_trans _ _ _ hr hyt))
      (C_seed s d _ z (lt_trans _ _ _ hz hyt))
  refine ⟨d, hdc, hd, rfl, psi_closed s k d p hpC hpk, fun d' hd'c hd' hpd' => ?_⟩
  exact hmin d' hd'c hd' (lt_trans _ _ _ (psi_lt s p e (regularIndex_regular s p hp.1)) hpd')

/-- A proper collapse at an index `p ≥ k` lies below `psi k (succ e)`. -/
theorem psi_succ_gt_of_proper (s : Supply) (k p e : O) (hk : RegularIndex s k)
    (hp : ProperCollapse s p e) (hkp : k ≤ p) (hlt : psi s p e < k) :
    psi s p e < psi s k (succ e) := by
  rcases hkp with hkp | rfl
  · apply lt_of_not_ge'
    intro hle
    rcases hle with hle | heq
    · have hex : ∃ x, C s e (psi s k (succ e)) x ∧ x < p ∧ psi s k (succ e) ≤ x := by
        apply Classical.byContradiction
        intro hnot
        apply (not_lt_iff_le _ _).mpr _ hle
        apply psi_min s p e
        refine ⟨Or.inl (lt_trans _ _ _ (psi_lt s k _ (regularIndex_regular s k hk)) hkp), ?_⟩
        intro x hx hxp
        exact lt_of_not_ge' (fun hge => hnot ⟨x, hx, hxp, hge⟩)
      obtain ⟨x, hx, hxp, hge⟩ := hex
      have hxlt : x < psi s p e := psi_closed s p e x (C_mono_seed s e _ _ (Or.inl hle) x hx) hxp
      have hx' : C s (succ e) (psi s k (succ e)) x :=
        C_mono_argument s e (succ e) _ (Or.inl (lt_succ_self e)) x hx
      exact (not_lt_iff_le _ _).mpr hge (psi_closed s k _ x hx' (lt_trans _ _ _ hxlt hlt))
    · obtain ⟨r, z, hI, hr, hz⟩ := proper_index_params_below s p e hp
      have hpC : C s (succ e) (psi s k (succ e)) p := by
        rw [hI]
        exact C_index s _ _ r z (C_seed s _ _ r (heq ▸ hr)) (C_seed s _ _ z (heq ▸ hz))
      have heC : C s (succ e) (psi s k (succ e)) e := by
        rw [heq]
        exact C_mono_argument s e (succ e) _ (Or.inl (lt_succ_self e)) e hp.2.2
      have hval := C_collapse s (succ e) _ p e (lt_succ_self e) hp.1 hpC heC
      exact lt_irrefl _ (heq ▸ psi_closed s k _ _ hval (heq ▸ hlt))
  · rcases psi_mono s k e (succ e) (Or.inl (lt_succ_self e)) with h | h
    · exact h
    · exact False.elim
        (psi_ne_of_argument_lt s k e k (succ e) hp.1 hp.1 (lt_succ_self e) hp.2.1 hp.2.2 h)

/-- The separation value of a proper collapse at an index `p ≥ k` is the
collapse at the ceiling of the successor of its argument. -/
theorem IsSep.of_collapse_above {s : Supply} {c gamma k p e t : O} (hk : RegularIndex s k)
    (hp : ProperCollapse s p e) (hkp : k ≤ p) (hlt : psi s p e < k)
    (h : IsSep s c gamma k (psi s p e) t) :
    ∃ d1, IsCeil s c gamma (succ e) d1 ∧ d1 < c ∧ t = psi s k d1 := by
  obtain ⟨d, hdc, hd, rfl, hyt, hmin⟩ := h
  have hed : e < d := by
    apply lt_of_not_ge'
    intro hde
    apply (not_lt_iff_le _ _).mpr _ hyt
    rcases hkp with hkp | rfl
    · apply psi_min s k d (psi s p e)
      refine ⟨Or.inl hlt, fun x hx hxk => ?_⟩
      exact psi_closed s p e x (C_mono_argument s d e _ hde x hx) (lt_trans _ _ _ hxk hkp)
    · exact psi_mono s k d e hde
  obtain ⟨d1, hd1⟩ := IsCeil.exists s c gamma (succ e) ⟨d, hd, (succ_le_iff_lt _ _).mpr hed⟩
  have hd1d : d1 ≤ d := hd1.2.2 d hd ((succ_le_iff_lt _ _).mpr hed)
  have hd1c : d1 < c := lt_of_le_of_lt hd1d hdc
  have hgt : psi s p e < psi s k d1 :=
    lt_of_lt_of_le (psi_succ_gt_of_proper s k p e hk hp (hkp) hlt) (psi_mono s k _ d1 hd1.2.1)
  exact ⟨d1, hd1, hd1c, le_antisymm (hmin d1 hd1c hd1.1 hgt) (psi_mono s k d1 d hd1d)⟩

/-- Below the seed, the separation value is the collapse at zero or at the
successor of an argument which satisfies the argument condition below the
seed. -/
theorem IsSep.of_small {s : Supply} {c gamma k y t : O} (hc : 0 < c) (hyg : y < gamma)
    (h : IsSep s c gamma k y t) :
    ∃ d1, t = psi s k d1 ∧ d1 < c ∧ C s c gamma d1 ∧
      (d1 = 0 ∨ ∃ e', d1 = succ e' ∧ psi s k e' ≤ y ∧ C s e' (psi s k e') e') := by
  obtain ⟨d, hdc, hd, rfl, hyt, hmin⟩ := h
  have hex : ∃ e, y < psi s k e := ⟨d, hyt⟩
  have hspec := least_spec _ hex
  have hle : least (fun e => y < psi s k e) hex ≤ d := least_le _ hex hyt
  generalize least (fun e => y < psi s k e) hex = es at hspec hle
  have hesc : es < c := lt_of_le_of_lt hle hdc
  have hbelow : ∀ e', e' < es → psi s k e' ≤ y :=
    fun e' he' => (not_lt_iff_le _ _).mp (hspec.2 e' he')
  have hcases := least_exceeding_argument s k y es hspec.1 hbelow
  have hesC : C s c gamma es := by
    rcases hcases with h0 | ⟨e', rfl, hle', hmem⟩
    · rw [h0]
      exact C_zero s c gamma
    · apply C_succ s c gamma e' hc
      apply C_mono_argument s e' c gamma (Or.inl (lt_trans _ _ _ (lt_succ_self e') hesc))
      exact C_mono_seed s e' _ _ (Or.inl (lt_of_le_of_lt hle' hyg)) e' hmem
  exact ⟨es, le_antisymm (hmin es hesc hesC hspec.1) (psi_mono s k es d hle), hesc, hesC, hcases⟩

theorem IsSep.of_index {s : Supply} {c gamma k u v t : O} (hlt : I s u v < k)
    (h : IsSep s c gamma k (I s u v) t) : IsSep s c gamma k u t ∨ IsSep s c gamma k v t :=
  h.of_parts (rank_le_I s u v) (index_le_I s u v)
    (fun d hu hv => psi_closed s k d _
      (C_index s d _ u v (C_seed s d _ u hu) (C_seed s d _ v hv)) hlt)

end
end OCF.Denis
