import Multi.term3.Denis.Separation

/-! The ceiling invariant for the Jäger-style closure.

Fix a cutoff `a` with completeness below it, a seed `beta`, and a smaller
closure `C(c, gamma)` with `c < a` and `beta ≤ gamma`. Assume that collapses
with arguments below `c` already stay in `PC(a, beta)`. Then every element
`y` of `PC(a, beta)` has its ceiling in `C(c, gamma)` in `PC(a, beta)`, and
so is the least collapse value `psi k d` above `y` (`d` an argument of the
closure) for every regular `k` of the closure in `PC(a, beta)`. -/

namespace OCF.Denis
open Ordinal
noncomputable section

structure CeilCtx (s : Supply) (a beta c gamma : O) : Prop where
  below : CompleteBelow s a
  ca : c < a
  bg : beta ≤ gamma
  c0 : 0 < c
  Q : ∀ d, d < c → ∀ k, RegularIndex s k → PC s a beta k → PC s a beta d →
    PC s a beta (psi s k d)

def CeilInv (s : Supply) (a beta c gamma y : O) : Prop :=
  (∀ t, IsCeil s c gamma y t → PC s a beta t) ∧
  (∀ k t, RegularIndex s k → C s c gamma k → PC s a beta k → IsSep s c gamma k y t →
    PC s a beta t)

theorem PC_succ (s : Supply) (a beta x : O) (ha : 0 < a) (hx : PC s a beta x) :
    PC s a beta (succ x) := by
  have h := PC.add hx (PC_finite s a beta ha 1)
  change PC s a beta (x + succ 0) at h
  rwa [add_succ, add_zero] at h

namespace CeilCtx

variable {s : Supply} {a beta c gamma : O}

theorem a0 (h : CeilCtx s a beta c gamma) : 0 < a := lt_trans _ _ _ h.c0 h.ca

theorem D (h : CeilCtx s a beta c gamma) (x : O) (hx : C s c gamma x) : PC s c gamma x :=
  h.below c h.ca gamma x hx

theorem inv_zero (h : CeilCtx s a beta c gamma) : CeilInv s a beta c gamma 0 := by
  refine ⟨fun t ht => ?_, fun k t hk _ hkP hs => ?_⟩
  · rw [ht.of_mem (C_zero s c gamma)]
    exact .zero
  · obtain ⟨d, _, _, rfl, _, hmin⟩ := hs
    have hpos := psi_pos s k 0 (regular_pos (regularIndex_regular s k hk))
    rw [le_antisymm (hmin 0 h.c0 (C_zero s c gamma) hpos) (psi_mono s k 0 d (zero_le d))]
    exact h.Q 0 h.c0 k hk hkP .zero

theorem inv_small (h : CeilCtx s a beta c gamma) (y : O) (hy : y < beta) :
    CeilInv s a beta c gamma y := by
  have hyg : y < gamma := lt_of_lt_of_le hy h.bg
  refine ⟨fun t ht => ?_, fun k t hk _ hkP hs => ?_⟩
  · rw [ht.of_mem (C_seed s c gamma y hyg)]
    exact .seed hy
  · obtain ⟨d1, rfl, hd1c, _, hcases⟩ := hs.of_small h.c0 hyg
    apply h.Q d1 hd1c k hk hkP
    rcases hcases with rfl | ⟨e', rfl, hle, hmem⟩
    · exact .zero
    · apply PC_succ s a beta e' h.a0
      have hea : e' < a := lt_trans _ _ _ (lt_trans _ _ _ (lt_succ_self e') hd1c) h.ca
      have hC : C s e' beta e' := C_mono_seed s e' _ _ (Or.inl (lt_of_le_of_lt hle hy)) e' hmem
      exact PC.mono (Or.inl hea) (le_refl beta) (h.below e' hea beta e' hC)

theorem inv_add (_h : CeilCtx s a beta c gamma) (u v : O) (hu : CeilInv s a beta c gamma u)
    (hv : ∀ p w, v = p + w → CeilInv s a beta c gamma w) :
    CeilInv s a beta c gamma (u + v) := by
  refine ⟨fun t ht => ?_, fun k t hk hkD hkP hs => ?_⟩
  · obtain ⟨t1, ht1⟩ := IsCeil.exists s c gamma u ⟨t, ht.1, le_trans (le_add u v) ht.2.1⟩
    have ht1P := hu.1 t1 ht1
    by_cases hle : u + v ≤ t1
    · have hc : IsCeil s c gamma (u + v) t1 :=
        ⟨ht1.1, hle, fun d hd hyd => ht1.2.2 d hd (le_trans (le_add u v) hyd)⟩
      rw [ht.unique hc]
      exact ht1P
    · have hlt : t1 < u + v := lt_of_not_ge' hle
      obtain ⟨v1, hv1⟩ := exists_add_of_le u t1 ht1.2.1
      have hv1v : v1 ≤ v := by
        apply (not_lt_iff_le _ _).mp
        intro hvv
        exact hle (hv1 ▸ add_mono_right u (Or.inl hvv))
      obtain ⟨v2, hv2⟩ := exists_add_of_le v1 v hv1v
      have hsum : u + v = t1 + v2 := by rw [hv1, hv2, add_assoc]
      rw [hsum] at ht
      obtain ⟨t', ht', rfl⟩ := ht.add_left ht1.1
      exact PC.add ht1P ((hv v1 v2 hv2).1 t' ht')
  · rcases hs.of_add hk with hs' | hs'
    · exact hu.2 k t hk hkD hkP hs'
    · exact (hv 0 v (zero_add v).symm).2 k t hk hkD hkP hs'

/-- Index case with an `I` target. -/
theorem ceil_index_I (h : CeilCtx s a beta c gamma) (u v r z : O)
    (huP : PC s a beta u) (hvP : PC s a beta v)
    (hu : CeilInv s a beta c gamma u) (hv : CeilInv s a beta c gamma v)
    (ht : IsCeil s c gamma (I s u v) (I s r z)) (hyt : I s u v < I s r z)
    (hzy : z < I s u v) (hrD : C s c gamma r) (hzD : C s c gamma z) :
    PC s a beta (I s r z) := by
  classical
  rcases I_lt_cases s u v r z hyt with ⟨hur, hvt⟩ | ⟨rfl, hvz⟩ | ⟨_, hyz⟩
  · obtain ⟨r', hr'⟩ := IsCeil.exists s c gamma u ⟨r, hrD, Or.inl hur⟩
    have hr'P := hu.1 r' hr'
    rcases hr'.2.2 r hrD (Or.inl hur) with hlt | heq
    · obtain ⟨z', hz'⟩ := IsCeil.exists s c gamma v ⟨I s r z, ht.1, Or.inl hvt⟩
      rcases hz'.2.2 _ ht.1 (Or.inl hvt) with hz'lt | hz'eq
      · exfalso
        have hge := ht.2.2 _ (C_index s c gamma r' z' hr'.1 hz'.1) (I_mono_both s hr'.2.1 hz'.2.1)
        have hlt' : I s r' z' < I s r z := by
          rw [← I_rank_fixed s r' r z hlt]
          exact I_strict s r' hz'lt
        exact (not_lt_iff_le _ _).mpr hge hlt'
      · rw [← hz'eq]
        exact hv.1 z' hz'
    · rw [heq] at hr'P
      by_cases hz0 : z = 0
      · subst hz0
        exact .index hr'P .zero
      · by_cases hzs : ∃ z1, z = succ z1
        · obtain ⟨z1, rfl⟩ := hzs
          have hz1D : C s c gamma z1 := C_predecessor s c gamma z1 hzD
          have hLy := ht.gap _ (C_index s c gamma r z1 hrD hz1D) (I_strict s r (lt_succ_self z1))
          have hLv : I s r z1 ≤ v := by
            apply (not_lt_iff_le _ _).mp
            intro hvL
            have h1 : I s u v < I s u (I s r z1) := I_strict s u hvL
            rw [I_rank_fixed s u r z1 hur] at h1
            exact lt_asymm h1 hLy
          exact .index hr'P (PC_succ s a beta z1 h.a0 (PC_I_interval s a beta r z1 v hvP hLv hvt))
        · have hlim : IsLimit z := ⟨hz0, hzs⟩
          apply hv.1
          refine ⟨ht.1, Or.inl hvt, fun d hd hvd => ?_⟩
          apply (not_lt_iff_le _ _).mp
          intro hdt
          have hexw : ∃ w, d < I s r w := ⟨z, hdt⟩
          have hspec := least_spec _ hexw
          have hwle : least (fun w => d < I s r w) hexw ≤ z := least_le _ hexw hdt
          generalize least (fun w => d < I s r w) hexw = w2 at hspec hwle
          have hbelow2 : ∀ w, w < w2 → I s r w ≤ d :=
            fun w hw => (not_lt_iff_le _ _).mp (hspec.2 w hw)
          have hw2z : w2 < z := by
            rcases hwle with h' | h'
            · exact h'
            · exfalso
              subst h'
              exact (not_lt_iff_le _ _).mpr (I_limit_le_of_forall s r w2 d hlim hbelow2) hspec.1
          have key : ∃ w, w < z ∧ C s c gamma w ∧ d < I s r w := by
            by_cases hw0 : w2 = 0
            · exact ⟨0, (zero_lt_iff_ne_zero z).mpr hz0, C_zero s c gamma, hw0 ▸ hspec.1⟩
            · by_cases hws : ∃ w1, w2 = succ w1
              · obtain ⟨w1, rfl⟩ := hws
                have hw1D := C_I_interval s c gamma r w1 d hd (hbelow2 w1 (lt_succ_self w1)) hspec.1
                exact ⟨succ w1, hw2z, C_succ s c gamma w1 h.c0 hw1D, hspec.1⟩
              · exact False.elim ((not_lt_iff_le _ _).mpr
                  (I_limit_le_of_forall s r w2 d ⟨hw0, hws⟩ hbelow2) hspec.1)
          obtain ⟨w, hwz, hwD, hdw⟩ := key
          have hyw : I s u v < I s r w := by
            have h1 : I s u v < I s u (I s r w) := I_strict s u (lt_of_le_of_lt hvd hdw)
            rwa [I_rank_fixed s u r w hur] at h1
          exact (not_lt_iff_le _ _).mpr (ht.2.2 _ (C_index s c gamma r w hrD hwD) (Or.inl hyw))
            (I_strict s r hwz)
  · obtain ⟨z', hz'⟩ := IsCeil.exists s c gamma v ⟨z, hzD, Or.inl hvz⟩
    have hz'z : z' ≤ z := hz'.2.2 z hzD (Or.inl hvz)
    have hge := ht.2.2 _ (C_index s c gamma u z' hrD hz'.1) (I_mono s u hz'.2.1)
    have hzz' : z ≤ z' := (I_le_iff s u z z').mp hge
    rw [← le_antisymm hzz' hz'z] at hz'
    exact .index huP (hv.1 z hz')
  · exact False.elim (lt_asymm hyz hzy)

/-- Index case with a collapse target. The index of the target is
recovered first; then the target is the separation value of a part. -/
theorem ceil_index_psi (h : CeilCtx s a beta c gamma) (u v kap eta : O)
    (hvP : PC s a beta v)
    (hu : CeilInv s a beta c gamma u) (hv : CeilInv s a beta c gamma v)
    (ht : IsCeil s c gamma (I s u v) (psi s kap eta)) (hyt : I s u v < psi s kap eta)
    (hgy : gamma ≤ I s u v) (hetac : eta < c) (hp : ProperCollapse s kap eta)
    (hkD : C s c gamma kap) (heD : C s c gamma eta) :
    PC s a beta (psi s kap eta) := by
  classical
  have hkreg := regularIndex_regular s kap hp.1
  have htk : psi s kap eta < kap := psi_lt s kap eta hkreg
  have hyk : I s u v < kap := lt_trans _ _ _ hyt htk
  have hut : u ≤ psi s kap eta := le_trans (rank_le_I s u v) ht.2.1
  have hvt : v ≤ psi s kap eta := le_trans (index_le_I s u v) ht.2.1
  obtain ⟨r', hr'⟩ := IsCeil.exists s c gamma u ⟨_, ht.1, hut⟩
  obtain ⟨z', hz'⟩ := IsCeil.exists s c gamma v ⟨_, ht.1, hvt⟩
  by_cases hr'eq : r' = psi s kap eta
  · rw [← hr'eq]
    exact hu.1 r' hr'
  have hr'lt : r' < psi s kap eta := by
    rcases hr'.2.2 _ ht.1 hut with hlt | heq
    · exact hlt
    · exact absurd heq hr'eq
  by_cases hz'eq : z' = psi s kap eta
  · rw [← hz'eq]
    exact hv.1 z' hz'
  have hz'lt : z' < psi s kap eta := by
    rcases hz'.2.2 _ ht.1 hvt with hlt | heq
    · exact hlt
    · exact absurd heq hz'eq
  obtain ⟨rk, zk, hkI, hrk, hzk, hrkD, hzkD⟩ :=
    C_regular_normal_presentation s c gamma kap hkreg
      (le_trans hgy (Or.inl hyk)) hkD
  have hkC : C s eta (psi s kap eta) (I s rk zk) := hkI ▸ hp.2.1
  have hrk' : rk < I s rk zk := hkI ▸ hrk
  have hzk' : zk < I s rk zk := hkI ▸ hzk
  obtain ⟨hrkC, hzkC⟩ := C_normal_index_parameters s eta _ rk zk hrk' hzk' hkC
  have hrkt : rk < psi s kap eta := psi_closed s kap eta rk hrkC hrk
  have hzkt : zk < psi s kap eta := psi_closed s kap eta zk hzkC hzk
  have hzky := ht.gap zk hzkD hzkt
  have hge := ht.2.2 _ (C_index s c gamma r' z' hr'.1 hz'.1) (I_mono_both s hr'.2.1 hz'.2.1)
  have hkle : kap ≤ I s r' z' := by
    apply (not_lt_iff_le _ _).mp
    intro hlt
    have hC : C s eta (psi s kap eta) (I s r' z') :=
      C_index s eta _ r' z' (C_seed s eta _ r' hr'lt) (C_seed s eta _ z' hz'lt)
    exact (not_lt_iff_le _ _).mpr hge (psi_closed s kap eta _ hC hlt)
  have hz'k : z' < I s rk zk := hkI ▸ lt_trans _ _ _ hz'lt htk
  have hrkr' : rk ≤ r' := by
    apply (not_lt_iff_le _ _).mp
    intro hlt
    apply (not_lt_iff_le _ _).mpr hkle
    have h1 : I s r' z' < I s r' (I s rk zk) := I_strict s r' hz'k
    rw [I_rank_fixed s r' rk zk hlt] at h1
    exact hkI ▸ h1
  have hyk' : I s u v < I s rk zk := hkI ▸ hyk
  have hurk : u ≤ rk := by
    apply (not_lt_iff_le _ _).mp
    intro hlt
    rcases I_lt_cases s u v rk zk hyk' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h1⟩
    · exact lt_asymm h1 hlt
    · exact lt_irrefl _ (h1 ▸ hlt)
    · exact lt_asymm h1 hzky
  have hrkeq : rk = r' := le_antisymm hrkr' (hr'.2.2 rk hrkD hurk)
  have hrkP : PC s a beta rk := hrkeq ▸ hu.1 r' hr'
  have hkP : PC s a beta kap := by
    rw [hkI]
    rcases regular_I_argument s rk zk hzk' (hkI ▸ hkreg) with hz0 | ⟨z1, hz1⟩
    · rw [hz0]
      exact .index hrkP .zero
    · subst hz1
      have hz1D : C s c gamma z1 := C_predecessor s c gamma z1 hzkD
      have hLC : C s eta (psi s kap eta) (I s rk z1) :=
        C_index s eta _ rk z1 (C_seed s eta _ rk hrkt)
          (C_seed s eta _ z1 (lt_trans _ _ _ (lt_succ_self z1) hzkt))
      have hLk : I s rk z1 < kap := hkI ▸ I_strict s rk (lt_succ_self z1)
      have hLy := ht.gap _ (C_index s c gamma rk z1 hrkD hz1D) (psi_closed s kap eta _ hLC hLk)
      rcases hurk with hlt | rfl
      · have hLv : I s rk z1 ≤ v := by
          apply (not_lt_iff_le _ _).mp
          intro hvL
          have h1 : I s u v < I s u (I s rk z1) := I_strict s u hvL
          rw [I_rank_fixed s u rk z1 hlt] at h1
          exact lt_asymm h1 hLy
        have hvk : v < I s rk (succ z1) := lt_of_le_of_lt (index_le_I s u v) hyk'
        exact .index hrkP (PC_succ s a beta z1 h.a0 (PC_I_interval s a beta rk z1 v hvP hLv hvk))
      · have hvz : v < succ z1 := (I_lt_iff s u v _).mp hyk'
        have hle : I s u v ≤ I s u z1 := I_mono s u ((lt_succ_iff_le v z1).mp hvz)
        exact False.elim ((not_lt_iff_le _ _).mpr hle hLy)
  have hsep : IsSep s c gamma kap (I s u v) (psi s kap eta) :=
    ⟨eta, hetac, heD, rfl, hyt, fun d' hd'c hd' hyd' =>
      ht.2.2 _ (C_collapse s c gamma kap d' hd'c hp.1 hkD hd') (Or.inl hyd')⟩
  rcases hsep.of_index hyk with hs' | hs'
  · exact hu.2 kap _ hp.1 hkD hkP hs'
  · exact hv.2 kap _ hp.1 hkD hkP hs'

theorem inv_index (h : CeilCtx s a beta c gamma) (u v : O)
    (huP : PC s a beta u) (hvP : PC s a beta v)
    (hu : CeilInv s a beta c gamma u) (hv : CeilInv s a beta c gamma v) :
    CeilInv s a beta c gamma (I s u v) := by
  classical
  refine ⟨fun t ht => ?_, fun k t hk hkD hkP hs => ?_⟩
  · by_cases hyD : C s c gamma (I s u v)
    · rw [ht.of_mem hyD]
      exact .index huP hvP
    have hyt : I s u v < t := by
      rcases ht.2.1 with hlt | heq
      · exact hlt
      · exact absurd (heq ▸ ht.1) hyD
    have hgy : gamma ≤ I s u v :=
      (not_lt_iff_le _ _).mp (fun hlt => hyD (C_seed s c gamma _ hlt))
    rcases IsCeil.canonical s c gamma _ t h.D (I_addPrincipal s u v) hyD ht with
      ⟨r, z, rfl, _, hzy, hrD, hzD, _, _⟩ | ⟨kap, eta, rfl, hetac, hp, hkD, heD⟩
    · exact h.ceil_index_I u v r z huP hvP hu hv ht hyt hzy hrD hzD
    · exact h.ceil_index_psi u v kap eta hvP hu hv ht hyt hgy hetac hp hkD heD
  · have hlt : I s u v < k := by
      obtain ⟨d, _, _, rfl, hyt, _⟩ := hs
      exact lt_trans _ _ _ hyt (psi_lt s k d (regularIndex_regular s k hk))
    rcases hs.of_index hlt with hs' | hs'
    · exact hu.2 k t hk hkD hkP hs'
    · exact hv.2 k t hk hkD hkP hs'

theorem inv_collapse (h : CeilCtx s a beta c gamma) (p e : O) (hea : e < a)
    (hp : ProperCollapse s p e) (hpP : PC s a beta p) (heP : PC s a beta e)
    (hpI : CeilInv s a beta c gamma p) (heI : CeilInv s a beta c gamma e) :
    CeilInv s a beta c gamma (psi s p e) := by
  classical
  have hpreg := regularIndex_regular s p hp.1
  have hyp : psi s p e < p := psi_lt s p e hpreg
  refine ⟨fun t ht => ?_, fun k t hk hkD hkP hs => ?_⟩
  · by_cases hyD : C s c gamma (psi s p e)
    · rw [ht.of_mem hyD]
      exact .collapse hea hp hpP heP
    have hyt : psi s p e < t := by
      rcases ht.2.1 with hlt | heq
      · exact hlt
      · exact absurd (heq ▸ ht.1) hyD
    have hgy : gamma ≤ psi s p e :=
      (not_lt_iff_le _ _).mp (fun hlt => hyD (C_seed s c gamma _ hlt))
    have hcase : p < t → PC s a beta t := fun hpt =>
      hpI.1 t ⟨ht.1, Or.inl hpt, fun d hd hpd => ht.2.2 d hd (le_trans (Or.inl hyp) hpd)⟩
    rcases IsCeil.canonical s c gamma _ t h.D (psi_addPrincipal s p e hpreg) hyD ht with
      ⟨r, z, rfl, hry, hzy, _, _, _, _⟩ | ⟨kap, eta, rfl, hetac, hq, hkD, heD⟩
    · rcases lt_total p (I s r z) with hpt | hpt | htp
      · exact hcase hpt
      · rw [← hpt]
        exact hpP
      · have hmem : C s e (psi s p e) (I s r z) :=
          C_index s e _ r z (C_seed s e _ r hry) (C_seed s e _ z hzy)
        exact False.elim (lt_asymm hyt (psi_closed s p e _ hmem htp))
    · have hkreg := regularIndex_regular s kap hq.1
      have htk : psi s kap eta < kap := psi_lt s kap eta hkreg
      rcases lt_total p (psi s kap eta) with hpt | hpt | htp
      · exact hcase hpt
      · exact False.elim (psi_not_uncountableRegular s kap eta (hpt ▸ hpreg))
      · rcases lt_total p kap with hpk | hpk | hkp
        · obtain ⟨r, z, hI, hr, hz⟩ := proper_index_params_below s p e hp
          have hmem : C s eta (psi s kap eta) p := by
            rw [hI]
            exact C_index s eta _ r z (C_seed s eta _ r (lt_trans _ _ _ hr hyt))
              (C_seed s eta _ z (lt_trans _ _ _ hz hyt))
          exact False.elim (lt_asymm htp (psi_closed s kap eta p hmem hpk))
        · subst hpk
          have heta : e < eta := by
            apply lt_of_not_ge'
            intro hle
            exact (not_lt_iff_le _ _).mpr (psi_mono s p eta e hle) hyt
          obtain ⟨d0, hd0⟩ := IsCeil.exists s c gamma e ⟨eta, heD, Or.inl heta⟩
          have hd0eta : d0 ≤ eta := hd0.2.2 eta heD (Or.inl heta)
          have hd0c : d0 < c := lt_of_le_of_lt hd0eta hetac
          have hmemD : C s c gamma (psi s p d0) := C_collapse s c gamma p d0 hd0c hq.1 hkD hd0.1
          have hge := ht.2.2 _ hmemD (psi_mono s p e d0 hd0.2.1)
          rw [← le_antisymm (psi_mono s p d0 eta hd0eta) hge]
          exact h.Q d0 hd0c p hq.1 hpP (heI.1 d0 hd0)
        · obtain ⟨rk, zk, hkI, hrk, hzk, hrkD, hzkD⟩ :=
            C_regular_normal_presentation s c gamma kap hkreg
              (le_trans hgy (Or.inl (lt_trans _ _ _ hyt htk))) hkD
          have hkC : C s eta (psi s kap eta) (I s rk zk) := hkI ▸ hq.2.1
          obtain ⟨hrkC, hzkC⟩ := C_normal_index_parameters s eta _ rk zk (hkI ▸ hrk) (hkI ▸ hzk) hkC
          have hrky := ht.gap rk hrkD (psi_closed s kap eta rk hrkC hrk)
          have hzky := ht.gap zk hzkD (psi_closed s kap eta zk hzkC hzk)
          have hmem : C s e (psi s p e) kap := by
            rw [hkI]
            exact C_index s e _ rk zk (C_seed s e _ rk hrky) (C_seed s e _ zk hzky)
          exact False.elim (lt_asymm (lt_trans _ _ _ hyt htk) (psi_closed s p e kap hmem hkp))
  · have hyk : psi s p e < k := by
      obtain ⟨d, _, _, rfl, hyt, _⟩ := hs
      exact lt_trans _ _ _ hyt (psi_lt s k d (regularIndex_regular s k hk))
    rcases lt_total p k with hpk | hpk | hkp
    · exact hpI.2 k t hk hkD hkP (hs.of_collapse_below hp hpk)
    all_goals
      have hkp' : k ≤ p := by
        first
        | exact Or.inr hpk.symm
        | exact Or.inl hkp
      obtain ⟨d1, hd1, hd1c, rfl⟩ := hs.of_collapse_above hk hp hkp' hyk
      apply h.Q d1 hd1c k hk hkP
      by_cases heD : C s c gamma e
      · rw [hd1.of_mem (C_succ s c gamma e h.c0 heD)]
        exact PC_succ s a beta e h.a0 heP
      · apply heI.1 d1
        refine ⟨hd1.1, le_trans (Or.inl (lt_succ_self e)) hd1.2.1, fun d hd hed => ?_⟩
        apply hd1.2.2 d hd
        rcases hed with hlt | heq
        · exact (succ_le_iff_lt _ _).mpr hlt
        · exact absurd (heq ▸ hd) heD

/-- The ceiling invariant holds for every suffix of every element of the
Jäger-style closure. -/
theorem inv_all (h : CeilCtx s a beta c gamma) (y : O) (hy : PC s a beta y) :
    ∀ p w, y = p + w → CeilInv s a beta c gamma w := by
  induction hy with
  | zero =>
    intro p w heq
    have hw : w = 0 := le_antisymm (heq ▸ right_le_add p w) (zero_le w)
    rw [hw]
    exact h.inv_zero
  | seed hy =>
    intro p w heq
    exact h.inv_small w (lt_of_le_of_lt (heq ▸ right_le_add p w) hy)
  | @add u v hu hv ihu ihv =>
    intro p w heq
    rcases lt_total u p with hup | rfl | hpu
    · obtain ⟨p', hp'⟩ := exists_add_of_le u p (Or.inl hup)
      rw [hp', add_assoc] at heq
      exact ihv p' w (add_right_cancel heq)
    · rw [← add_right_cancel heq]
      exact ihv 0 v (zero_add v).symm
    · obtain ⟨u', hu'⟩ := exists_add_of_le p u (Or.inl hpu)
      rw [hu', add_assoc] at heq
      rw [← add_right_cancel heq]
      exact h.inv_add u' v (ihu p u' hu') ihv
  | @index u v hu hv ihu ihv =>
    intro p w heq
    rcases addPrincipal_suffix (I_addPrincipal s u v) heq with hw | hw
    · rw [hw]
      exact h.inv_zero
    · rw [hw]
      exact h.inv_index u v hu hv (ihu 0 u (zero_add u).symm) (ihv 0 v (zero_add v).symm)
  | @collapse k e he hp hk he' ihk ihe =>
    intro p w heq
    rcases addPrincipal_suffix (psi_addPrincipal s k e (regularIndex_regular s k hp.1)) heq with
      hw | hw
    · rw [hw]
      exact h.inv_zero
    · rw [hw]
      exact h.inv_collapse k e he hp hk he' (ihk 0 k (zero_add k).symm) (ihe 0 e (zero_add e).symm)

end CeilCtx

/-- Every collapse of parameters in the Jäger-style closure is again in it,
given completeness below the cutoff. -/
theorem pcCollapseStep_holds (s : Supply) : PCCollapseStep s := by
  intro a beta k b hbelow hk hkP hbP hba
  induction b using lt_wellFounded.induction generalizing k with
  | h b ih =>
    apply collapse_closed_of_ceiling s a beta k b hk hkP hbP hba
    intro hbg bstar hbs hbb hleast
    by_cases hb0 : b = 0
    · subst hb0
      rw [le_antisymm (hleast 0 (C_zero s 0 _) (le_refl _)) (zero_le bstar)]
      exact .zero
    · have hctx : CeilCtx s a beta b (psi s k b) :=
        { below := hbelow
          ca := hba
          bg := hbg
          c0 := (zero_lt_iff_ne_zero b).mpr hb0
          Q := fun d hd k' hk' hk'P hdP => ih d hd k' hk' hk'P hdP (lt_trans _ _ _ hd hba) }
      exact (hctx.inv_all b hbP 0 b (zero_add b).symm).1 bstar ⟨hbs, hbb, hleast⟩

/-- Every element of Denis's closure has a derivation using only proper
collapses (completeness of the Jäger-style closure). -/
theorem properClosureComplete (s : Supply) : ProperClosureComplete s :=
  properClosureComplete_of_collapse_step s (pcCollapseStep_holds s)

/-- General parameter recovery: a proper collapse above the seed has its
index and argument in the closure, and its argument below the cutoff.
There is no bound on the argument in terms of the index. -/
theorem C_proper_collapse_parameters (s : Supply) (k a cutoff beta : O)
    (hp : ProperCollapse s k a) (hb : beta ≤ psi s k a)
    (hx : C s cutoff beta (psi s k a)) :
    a < cutoff ∧ C s cutoff beta k ∧ C s cutoff beta a :=
  C_proper_collapse_parameters_of_complete s (properClosureComplete s) k a cutoff beta hp hb hx

end
end OCF.Denis
