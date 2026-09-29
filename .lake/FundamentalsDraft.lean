import Multi.term2
open T

theorem T.ofNat_lt_succ (n : Nat) : T.ofNat n < T.ofNat (n + 1) := by
  induction n with
  | zero => exact T.lt.Z_lt_P Z Z Z
  | succ n ih => exact T.lt.p_third _ _ _ _ ih

theorem T.mul_principal_strict (a b : T) (n : Nat) :
    T.mul (P a b Z) (T.ofNat n) < T.mul (P a b Z) (T.ofNat (n + 1)) := by
  induction n with
  | zero => exact T.lt.Z_lt_P a b Z
  | succ n ih =>
    rw [T.mul_principal_ofNat_succ, T.mul_principal_ofNat_succ]
    exact T.lt.p_third _ _ _ _ ih

theorem T.collapsing_iterates_strict (b l : T) (hd : T.dom b = .Ω l) (n : Nat) :
    T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n)) <
      T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat (n + 1))) := by
  let F := fun x => P (T.fund l Z) (T.fund b x) Z
  have hi : ∀ n, T.iter F (T.ofNat n) < T.iter F (T.ofNat (n + 1)) := by
    intro n
    induction n with
    | zero => exact T.lt.Z_lt_P _ _ Z
    | succ n ih => exact T.lt.p_second _ _ _ _ _ (T.fund_omega_strict b l hd _ _ ih)
  exact T.fund_omega_strict b l hd _ _ (hi n)

theorem T.fund_countable_limit_strict (s : T) (hd : T.dom s = .ω) (n : Nat) :
    T.fund s (T.ofNat n) < T.fund s (T.ofNat (n + 1)) := by
  induction s with
  | Z => cases hd
  | P a b c ih0 ih1 ih2 =>
    by_cases hc : c = Z
    · cases hc
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl, T.fund, ite_eq_left rfl]
      cases hb : T.dom b with
      | Zero =>
        rw [hb] at hd
        cases ha : T.dom a with
        | Zero => rw [ha] at hd; cases hd
        | One => rw [ha] at hd; cases hd
        | ω => exact T.lt.p_first _ _ _ _ _ _ (ih0 ha)
        | Ω l => rw [ha] at hd; cases hd
      | One => exact T.mul_principal_strict a (T.fund b Z) n
      | ω => exact T.lt.p_second _ _ _ _ _ (ih1 hb)
      | Ω l =>
        rw [hb] at hd
        change (if a < l then Dom.ω else Dom.Ω l) = Dom.ω at hd
        change (if a < l then P a (T.fund b
          (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n))) Z
          else P a (T.fund b (T.ofNat n)) Z) <
          (if a < l then P a (T.fund b
          (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat (n + 1)))) Z
          else P a (T.fund b (T.ofNat (n + 1))) Z)
        by_cases hal : a < l
        · rw [ite_eq_left hal, ite_eq_left hal]
          exact T.lt.p_second _ _ _ _ _ (T.collapsing_iterates_strict b l hb n)
        · rw [ite_eq_right hal] at hd; cases hd
    · rw [T.dom, ite_eq_right hc] at hd
      rw [T.fund, ite_eq_right hc, T.fund, ite_eq_right hc]
      exact T.lt.p_third _ _ _ _ (ih2 hd)

theorem T.fund_ofNat_mono (s : T) (n m : Nat) (hnm : n ≤ m) :
    T.fund s (T.ofNat n) ≤ T.fund s (T.ofNat m) := by
  cases hd : T.dom s with
  | Zero => rw [T.dom_eq_zero s hd, T.fund_Z, T.fund_Z]; exact Or.inr rfl
  | One => rw [(T.fund_one_properties s hd).1 (T.ofNat n),
      (T.fund_one_properties s hd).1 (T.ofNat m)]; exact Or.inr rfl
  | ω =>
    exact T.sequence_le_of_step (fun i => T.fund s (T.ofNat i))
      (T.fund_countable_limit_strict s hd) n m hnm
  | Ω l =>
    apply T.sequence_le_of_step (fun i => T.fund s (T.ofNat i)) _ n m hnm
    intro i
    exact T.fund_omega_strict s l hd _ _ (T.ofNat_lt_succ i)

theorem T.GBound_fund_regular_eventually (s u : T) (hs : T.isNF s)
    (hd : T.dom s = .ω) (hG : T.GBound u s s) :
    ∃ N, ∀ n, N ≤ n → T.GBound u (T.fund s (T.ofNat n)) (T.fund s (T.ofNat n)) := by
  have hno : ∀ l, T.dom s ≠ .Ω l := by intro l hl; rw [hd] at hl; cases hl
  let f := fun n => T.fund s (T.ofNat n)
  have hcover : ∀ x, x ∈ T.G u s → ∃ n, x < f n := by
    intro x hx
    have hxNF := (T.mem_G_properties u s x hs hx).1
    cases T.fund_nonomega_cofinal s hs hno x hxNF (hG x hx) with
    | intro n hn =>
      exact ⟨n + 1, lt_of_le_of_lt_thm T x (f n) (f (n + 1)) hn
        (T.fund_countable_limit_strict s hd n)⟩
  cases T.list_bound_sequence (T.G u s) f (T.fund_ofNat_mono s) hcover with
  | intro N hN =>
    refine ⟨N, ?_⟩
    intro n hn
    have hsource : T.GBound u s (f n) := by
      intro x hx
      exact lt_of_lt_of_le_thm T x (f N) (f n) (hN x hx) (T.fund_ofNat_mono s N n hn)
    exact T.GBound_fund_ofNat s hs u (f n) hsource n

theorem T.GBound_of_le_self (u s : T) (hs : T.isNF s)
    (h : ∀ x, x ∈ T.G u s → x ≤ s) : T.GBound u s s := by
  intro x hx
  cases h x hx with
  | inl hlt => exact hlt
  | inr heq =>
    have hsize := (T.mem_G_properties u s x hs hx).2
    rw [heq] at hsize
    exact False.elim (Nat.lt_irrefl _ hsize)

theorem T.GBound_fund_regular_of_le (s u t : T) (hs : T.isNF s)
    (hresult : T.isNF (T.fund s t))
    (hd : ∀ l, T.dom s = .Ω l → t < P l Z Z)
    (hsource : ∀ x, x ∈ T.G u s → x ≤ T.fund s t)
    (hinput : ∀ x, x ∈ T.G u t → x ≤ T.fund s t) :
    T.GBound u (T.fund s t) (T.fund s t) := by
  have hG : T.GBound u (T.fund s t) (T.fund s t + P Z Z Z) := by
    apply T.GBound_fund s hs u (T.fund s t + P Z Z Z) t hd
    · intro x hx
      exact lt_of_le_of_lt_thm T x (T.fund s t) _ (hsource x hx) (T.lt_add_one _)
    · intro x hx
      exact lt_of_le_of_lt_thm T x (T.fund s t) _ (hinput x hx) (T.lt_add_one _)
  apply T.GBound_of_le_self u (T.fund s t) hresult
  intro x hx
  have hle := (T.fund_one_properties (T.fund s t + P Z Z Z)
    (T.dom_add_one (T.fund s t))).2.2.1 x (hG x hx)
  rw [T.fund_add_one] at hle
  exact hle

theorem T.mem_G_size (u s x : T) (hx : x ∈ T.G u s) : x.size < s.size := by
  induction s generalizing x with
  | Z => exact False.elim (List.not_mem_nil hx)
  | P a b c ih0 ih1 ih2 =>
    by_cases hu : u ≤ a
    · rw [T.G_P_of_le u a b c hu] at hx
      cases List.mem_append.mp hx with
      | inr hxc => exact Nat.lt_trans (ih2 x hxc) (T.size_lt_size_P_third a b c)
      | inl hx01 =>
        cases List.mem_append.mp hx01 with
        | inr hxb => exact Nat.lt_trans (ih1 x hxb) (T.size_lt_size_P_second a b c)
        | inl hx0 =>
          cases List.mem_append.mp hx0 with
          | inr hxa => exact Nat.lt_trans (ih0 x hxa) (T.size_lt_size_P_first a b c)
          | inl hxb => rw [List.mem_singleton.mp hxb]; exact T.size_lt_size_P_second a b c
    · rw [T.G_P_of_not_le u a b c hu] at hx
      exact Nat.lt_trans (ih2 x hx) (T.size_lt_size_P_third a b c)

theorem T.GBound_failure (u s b : T) (h : ¬ T.GBound u s b) :
    ∃ x, x ∈ T.G u s ∧ b ≤ x := by
  have findBad : ∀ xs : List T, (¬ ∀ x, x ∈ xs → x < b) → ∃ x, x ∈ xs ∧ b ≤ x := by
    intro xs
    induction xs with
    | nil =>
      intro hn
      apply False.elim
      apply hn
      intro x hx
      exact False.elim (List.not_mem_nil hx)
    | cons a xs ih =>
      intro hn
      by_cases hab : a < b
      · have htail : ¬ ∀ x, x ∈ xs → x < b := by
          intro ht
          apply hn
          intro x hx
          cases List.mem_cons.mp hx with
          | inl heq => rw [heq]; exact hab
          | inr hxt => exact ht x hxt
        cases ih htail with
        | intro x hx => exact ⟨x, List.mem_cons_of_mem a hx.1, hx.2⟩
      · exact ⟨a, List.mem_cons_self, T.le_of_not_lt a b hab⟩
  exact findBad (T.G u s) h

/-- A bound formulation of Buchholz's support interpolation relation. -/
def T.SupportStep (z b a : T) : Prop := b < a ∧
  ∀ u c k, b ≤ c → c ≤ a → T.GBound u c k → T.GBound u z k → Z < k → T.GBound u b k

theorem T.SupportStep.regular {z b a : T} (h : T.SupportStep z b a) (u : T)
    (ha : T.GBound u a a) (hz : T.GBound u z b) : T.GBound u b b := by
  cases b with
  | Z => exact T.GBound_zero u Z
  | P b0 b1 b2 =>
    let b := P b0 b1 b2
    have hbpos : Z < b := T.lt.Z_lt_P b0 b1 b2
    have hba : b < a := h.1
    have hza : T.GBound u z a := by
      intro x hx
      exact T.lt_trans x b a (hz x hx) hba
    have hGa : T.GBound u b a := h.2 u a a (Or.inl hba) (Or.inr rfl) ha hza
      (T.lt_trans Z b a hbpos hba)
    have descend : ∀ c, b ≤ c → c < a → T.GBound u c a →
        ∃ d, b ≤ d ∧ d ≤ a ∧ T.GBound u d b := by
      intro c hbc hca hcG
      induction c using (measure T.size).wf.induction with
      | h c ih =>
        by_cases hgood : T.GBound u c b
        · exact ⟨c, hbc, Or.inl hca, hgood⟩
        · cases T.GBound_failure u c b hgood with
          | intro d hd =>
            exact ih d (T.mem_G_size u c d hd.1) hd.2 (hcG d hd.1)
              (T.GBound_mem u c d a hcG hd.1)
    cases descend b (Or.inr rfl) hba hGa with
    | intro d hd => exact h.2 u d b hd.1 hd.2.1 hd.2.2 hz hbpos

theorem T.SupportStep.zero (z a : T) (ha : Z < a) : T.SupportStep z Z a := by
  refine ⟨ha, ?_⟩
  intro u c k hbc hca hc hz hk
  exact T.GBound_zero u k

theorem T.SupportStep.input (b a : T) (ha : b < a) : T.SupportStep b b a := by
  refine ⟨ha, ?_⟩
  intro u c k hbc hca hc hz hk
  exact hz

theorem T.first_le_of_P_le (a b c d e f : T) (h : P a b c ≤ P d e f) : a ≤ d :=
  T.first_le_of_head_le a b Z d e (T.head_mono (P a b c) (P d e f) h)

theorem T.second_le_of_P_le (a b c e f : T) (h : P a b c ≤ P a e f) : b ≤ e := by
  cases h with
  | inr heq => cases heq; exact Or.inr rfl
  | inl hlt =>
    cases lt_inv a b c a e f hlt with
    | inl h0 => exact False.elim (T.lt_irrefl a h0)
    | inr hrest =>
      cases hrest with
      | inl h1 => exact Or.inl h1.2
      | inr h2 => exact Or.inr h2.2.1

theorem T.third_le_of_P_le (a b c f : T) (h : P a b c ≤ P a b f) : c ≤ f := by
  cases h with
  | inr heq => cases heq; exact Or.inr rfl
  | inl hlt =>
    cases lt_inv a b c a b f hlt with
    | inl h0 => exact False.elim (T.lt_irrefl a h0)
    | inr hrest =>
      cases hrest with
      | inl h1 => exact False.elim (T.lt_irrefl b h1.2)
      | inr h2 => exact Or.inl h2.2.2

theorem T.SupportStep.principal {z b a : T} (h : T.SupportStep z b a) (v : T) :
    T.SupportStep z (P v b Z) (P v a Z) := by
  refine ⟨T.lt.p_second _ _ _ _ _ h.1, ?_⟩
  intro u c k hbc hca hc hz hk
  cases c with
  | Z =>
    cases hbc with
    | inl hlt => exact False.elim (lt_Z_inv _ hlt)
    | inr heq => cases heq
  | P c0 c1 c2 =>
    have heq := partial_order.antisymm c0 v
      (T.first_le_of_P_le c0 c1 c2 v a Z hca) (T.first_le_of_P_le v b Z c0 c1 c2 hbc)
    cases heq
    have hb1 := T.second_le_of_P_le v b Z c1 c2 hbc
    have h1a := T.second_le_of_P_le v c1 c2 a Z hca
    apply (T.GBound_P u v b Z k).mpr
    refine ⟨?_, T.GBound_zero u k⟩
    intro hu
    have hp := ((T.GBound_P u v c1 c2 k).mp hc).1 hu
    exact ⟨lt_of_le_of_lt_thm T b c1 k hb1 hp.1, hp.2.1,
      h.2 u c1 k hb1 h1a hp.2.2 hz hk⟩

theorem T.SupportStep.index {z b a : T} (h : T.SupportStep z b a) :
    T.SupportStep z (P b Z Z) (P a Z Z) := by
  refine ⟨T.lt.p_first _ _ _ _ _ _ h.1, ?_⟩
  intro u c k hbc hca hc hz hk
  cases c with
  | Z =>
    cases hbc with
    | inl hlt => exact False.elim (lt_Z_inv _ hlt)
    | inr heq => cases heq
  | P c0 c1 c2 =>
    have hb0 := T.first_le_of_P_le b Z Z c0 c1 c2 hbc
    have h0a := T.first_le_of_P_le c0 c1 c2 a Z Z hca
    apply (T.GBound_P u b Z Z k).mpr
    refine ⟨?_, T.GBound_zero u k⟩
    intro hu
    have huc := partial_order.trans u b c0 hu hb0
    have hp := ((T.GBound_P u c0 c1 c2 k).mp hc).1 huc
    exact ⟨hk, h.2 u c0 k hb0 h0a hp.2.1 hz hk, T.GBound_zero u k⟩

theorem T.SupportStep.tail {z b a : T} (h : T.SupportStep z b a) (v w : T) :
    T.SupportStep z (P v w b) (P v w a) := by
  refine ⟨T.lt.p_third _ _ _ _ h.1, ?_⟩
  intro u c k hbc hca hc hz hk
  cases c with
  | Z =>
    cases hbc with
    | inl hlt => exact False.elim (lt_Z_inv _ hlt)
    | inr heq => cases heq
  | P c0 c1 c2 =>
    have h0 := partial_order.antisymm c0 v
      (T.first_le_of_P_le c0 c1 c2 v w a hca) (T.first_le_of_P_le v w b c0 c1 c2 hbc)
    cases h0
    have h1 := partial_order.antisymm c1 w
      (T.second_le_of_P_le v c1 c2 w a hca) (T.second_le_of_P_le v w b c1 c2 hbc)
    cases h1
    have hb2 := T.third_le_of_P_le v w b c2 hbc
    have h2a := T.third_le_of_P_le v w c2 a hca
    have hp := (T.GBound_P u v w c2 k).mp hc
    exact (T.GBound_P u v w b k).mpr ⟨hp.1, h.2 u c2 k hb2 h2a hp.2 hz hk⟩

theorem T.fund_omega_supportStep (s l t : T) (hd : T.dom s = .Ω l)
    (ht : t < P l Z Z) : T.SupportStep t (T.fund s t) s := by
  induction s generalizing l with
  | Z => cases hd
  | P a b c ih0 ih1 ih2 =>
    by_cases hc : c = Z
    · cases hc
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl]
      cases hb : T.dom b with
      | Zero =>
        rw [hb] at hd
        have hbZ := T.dom_eq_zero b hb
        cases hbZ
        cases ha : T.dom a with
        | Zero => rw [ha] at hd; cases hd
        | One =>
          rw [ha] at hd
          cases hd
          exact T.SupportStep.input t (P a Z Z) ht
        | ω => rw [ha] at hd; cases hd
        | Ω m =>
          rw [ha] at hd
          cases hd
          exact (ih0 l ha ht).index
      | One => rw [hb] at hd; cases hd
      | ω => rw [hb] at hd; cases hd
      | Ω m =>
        rw [hb] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        change T.SupportStep t (if a < m then
          P a (T.fund b (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) t)) Z
          else P a (T.fund b t) Z) (P a b Z)
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham] at hd
          cases hd
          rw [ite_eq_right ham]
          exact (ih1 l hb ht).principal a
    · rw [T.dom, ite_eq_right hc] at hd
      rw [T.fund, ite_eq_right hc]
      exact (ih2 l hd ht).tail a b

theorem T.fund_omega_isNF (s l t : T) (hs : T.isNF s) (hd : T.dom s = .Ω l)
    (htNF : T.isNF t) (ht : t < P l Z Z) : T.isNF (T.fund s t) := by
  induction hs generalizing l with
  | z => cases hd
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hs := T.isNF.p a b c ha hb hc hreg hhead
    by_cases hcZ : c = Z
    · cases hcZ
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl]
      cases hbdom : T.dom b with
      | Zero =>
        rw [hbdom] at hd
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        cases hadom : T.dom a with
        | Zero => rw [hadom] at hd; cases hd
        | One => exact htNF
        | ω => rw [hadom] at hd; cases hd
        | Ω m =>
          rw [hadom] at hd
          cases hd
          exact T.isNF_index (T.fund a t) (ih0 l hadom ht)
      | One => rw [hbdom] at hd; cases hd
      | ω => rw [hbdom] at hd; cases hd
      | Ω m =>
        rw [hbdom] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        change T.isNF (if a < m then
          P a (T.fund b (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) t)) Z
          else P a (T.fund b t) Z)
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham] at hd
          cases hd
          rw [ite_eq_right ham]
          have hta : t < P a Z Z := lt_of_lt_of_le_thm T t (P l Z Z) (P a Z Z) ht
            (T.index_le_P l a Z Z (T.le_of_not_lt a l ham))
          have hinput := T.GBound_below_index a t (T.fund b t) htNF hta
          have hregular := (T.fund_omega_supportStep b l t hbdom ht).regular a hreg hinput
          exact T.isNF.p a (T.fund b t) Z ha (ih1 l hbdom ht) T.isNF.z hregular (T.Z_le _)
    · have hdc : T.dom c = .Ω l := by
        rw [T.dom, ite_eq_right hcZ] at hd
        exact hd
      apply T.fund_nonzero_tail_isNF a b c t hs hcZ (ih2 l hdc ht)
      intro m hm
      rw [hdc] at hm
      cases hm
      exact ht

theorem T.lt_predecessor_index_of_size (l q r : T) (hl : T.dom l = .One)
    (hr : r < P l Z Z) (hsize : r.size < (T.fund l Z).size) :
    r < P (T.fund l Z) q Z := by
  cases r with
  | Z => exact T.lt.Z_lt_P _ q Z
  | P r0 r1 r2 =>
    have hr0 : r0 < l := by
      cases hr with
      | p_first _ _ _ _ _ _ h0 => exact h0
      | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
      | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
    cases (T.fund_one_properties l hl).2.2.1 r0 hr0 with
    | inl hlt => exact T.lt.p_first _ _ _ _ _ _ hlt
    | inr heq =>
      have hsmall := Nat.lt_trans (T.size_lt_size_P_first r0 r1 r2) hsize
      rw [heq] at hsmall
      exact False.elim (Nat.lt_irrefl _ hsmall)

theorem T.fund_omega_dominates_small (s l q r : T) (hd : T.dom s = .Ω l)
    (hr : r < s) (hsize : r.size < (T.fund l Z).size) :
    r < T.fund s (P (T.fund l Z) q Z) := by
  induction s generalizing l r with
  | Z => exact False.elim (lt_Z_inv r hr)
  | P a b c ih0 ih1 ih2 =>
    by_cases hc : c = Z
    · cases hc
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl]
      cases hb : T.dom b with
      | Zero =>
        rw [hb] at hd
        have hbZ := T.dom_eq_zero b hb
        cases hbZ
        cases ha : T.dom a with
        | Zero => rw [ha] at hd; cases hd
        | One =>
          rw [ha] at hd
          cases hd
          exact T.lt_predecessor_index_of_size a q r ha hr hsize
        | ω => rw [ha] at hd; cases hd
        | Ω m =>
          rw [ha] at hd
          cases hd
          cases r with
          | Z => exact T.lt.Z_lt_P _ Z Z
          | P r0 r1 r2 =>
            have hr0 : r0 < a := by
              cases hr with
              | p_first _ _ _ _ _ _ h0 => exact h0
              | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
              | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
            exact T.lt.p_first _ _ _ _ _ _ (ih0 l r0 ha hr0
              (Nat.lt_trans (T.size_lt_size_P_first r0 r1 r2) hsize))
      | One => rw [hb] at hd; cases hd
      | ω => rw [hb] at hd; cases hd
      | Ω m =>
        rw [hb] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        change r < (if a < m then P a (T.fund b
          (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) (P (T.fund l Z) q Z))) Z
          else P a (T.fund b (P (T.fund l Z) q Z)) Z)
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham] at hd
          cases hd
          rw [ite_eq_right ham]
          cases r with
          | Z => exact T.lt.Z_lt_P a _ Z
          | P r0 r1 r2 =>
            cases hr with
            | p_first _ _ _ _ _ _ h0 => exact T.lt.p_first _ _ _ _ _ _ h0
            | p_second _ _ _ _ _ h1 =>
              exact T.lt.p_second _ _ _ _ _ (ih1 l r1 hb h1
                (Nat.lt_trans (T.size_lt_size_P_second a r1 r2) hsize))
            | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
    · rw [T.dom, ite_eq_right hc] at hd
      rw [T.fund, ite_eq_right hc]
      cases r with
      | Z => exact T.lt.Z_lt_P a b _
      | P r0 r1 r2 =>
        cases hr with
        | p_first _ _ _ _ _ _ h0 => exact T.lt.p_first _ _ _ _ _ _ h0
        | p_second _ _ _ _ _ h1 => exact T.lt.p_second _ _ _ _ _ h1
        | p_third _ _ _ _ h2 =>
          exact T.lt.p_third _ _ _ _ (ih2 l r2 hd h2
            (Nat.lt_trans (T.size_lt_size_P_third a b r2) hsize))

theorem T.fund_collapsing_principal_isNF (a b l : T) (hs : T.isNF (P a b Z))
    (hd : T.dom b = .Ω l) (hal : a < l) (n : Nat) :
    T.isNF (T.fund (P a b Z) (T.ofNat n)) := by
  cases hs with
  | p _ _ _ ha hb hZ hreg hhead =>
    let F := fun x => P (T.fund l Z) (T.fund b x) Z
    let xs := fun m => T.iter F (T.ofNat m)
    let bs := fun m => T.fund b (xs m)
    have hlNF := T.dom_omega_index_isNF b l hb hd
    have hlone := T.dom_omega_index_one b l hd
    have hlpNF := T.fund_one_isNF l hlNF hlone Z
    have hlne : l ≠ Z := by intro heq; rw [heq] at hlone; cases hlone
    have hlp := T.fund_lt_of_domain l Z hlne (fun m _ => T.lt.Z_lt_P m Z Z)
    have hap := (T.fund_one_properties l hlone).2.2.1 a hal
    have hindex : T.GBound a (T.fund l Z) b :=
      T.GBound_fund_one a l b hlone (T.GBound_dom_index b l a b hb hd (Or.inl hal) hreg)
    have hxs : ∀ m, xs m < P l Z Z := by
      intro m
      cases m with
      | zero => exact T.lt.Z_lt_P l Z Z
      | succ m => exact T.lt.p_first _ _ _ _ _ _ hlp
    have hbs : ∀ m, bs m < bs (m + 1) := T.collapsing_iterates_strict b l hd
    have hinv : ∀ m, T.isNF (xs m) ∧ T.isNF (bs m) ∧ T.GBound a (bs m) (bs m) := by
      intro m
      induction m with
      | zero =>
        exact ⟨T.isNF.z, T.fund_omega_isNF b l Z hb hd T.isNF.z (hxs 0),
          (T.fund_omega_supportStep b l Z hd (hxs 0)).regular a hreg (T.GBound_zero a _)⟩
      | succ m ih =>
        have hxNF : T.isNF (xs (m + 1)) :=
          T.isNF.p (T.fund l Z) (bs m) Z hlpNF ih.2.1 T.isNF.z
            (T.GBound_index_mono (bs m) a (T.fund l Z) (bs m) hap ih.2.2) (T.Z_le _)
        have hbNF := T.fund_omega_isNF b l (xs (m + 1)) hb hd hxNF (hxs (m + 1))
        have hinput : T.GBound a (xs (m + 1)) (bs (m + 1)) := by
          apply (T.GBound_P a (T.fund l Z) (bs m) Z (bs (m + 1))).mpr
          refine ⟨?_, T.GBound_zero a _⟩
          intro hap'
          refine ⟨hbs m, ?_, ?_⟩
          · intro x hx
            exact T.fund_omega_dominates_small b l (bs m) x hd (hindex x hx)
              (T.mem_G_size a (T.fund l Z) x hx)
          · intro x hx
            exact T.lt_trans _ _ _ (ih.2.2 x hx) (hbs m)
        exact ⟨hxNF, hbNF,
          (T.fund_omega_supportStep b l (xs (m + 1)) hd (hxs (m + 1))).regular a hreg hinput⟩
    rw [T.fund, ite_eq_left rfl, hd]
    change T.isNF (if a < l then P a (bs n) Z else P a (T.fund b (T.ofNat n)) Z)
    rw [ite_eq_left hal]
    exact T.isNF.p a (bs n) Z ha (hinv n).2.1 T.isNF.z (hinv n).2.2 (T.Z_le _)

theorem T.GBound_predecessor_of_fund_interval (s : T) (hs : T.isNF s) (l u q c k : T)
    (hd : T.dom s = .Ω l) (hul : u < l)
    (hlo : T.fund s (P (T.fund l Z) q Z) ≤ c) (hhi : c ≤ s)
    (hG : T.GBound u c k) : T.GBound u (T.fund l Z) k := by
  induction hs generalizing l c with
  | z => cases hd
  | p a b d ha hb hdn hreg hhead ih0 ih1 ih2 =>
    have hlone := T.dom_omega_index_one (P a b d) l hd
    have hlne : l ≠ Z := by intro heq; rw [heq] at hlone; cases hlone
    have hlp := T.fund_lt_of_domain l Z hlne (fun m _ => T.lt.Z_lt_P m Z Z)
    have hup := (T.fund_one_properties l hlone).2.2.1 u hul
    by_cases hdZ : d = Z
    · cases hdZ
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl] at hlo
      cases hbdom : T.dom b with
      | Zero =>
        rw [hbdom] at hd hlo
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        cases hadom : T.dom a with
        | Zero => rw [hadom] at hd; cases hd
        | One =>
          rw [hadom] at hd hlo
          cases hd
          cases c with
          | Z =>
            cases hlo with
            | inl hlt => exact False.elim (lt_Z_inv _ hlt)
            | inr heq => cases heq
          | P c0 c1 c2 =>
            have hp0 := T.first_le_of_P_le (T.fund a Z) q Z c0 c1 c2 hlo
            have h0a := T.first_le_of_P_le c0 c1 c2 a Z Z hhi
            have huc := partial_order.trans u (T.fund a Z) c0 hup hp0
            have hGc0 := (((T.GBound_P u c0 c1 c2 k).mp hG).1 huc).2.1
            cases h0a with
            | inl hlt =>
              have h0p := (T.fund_one_properties a hadom).2.2.1 c0 hlt
              have heq := partial_order.antisymm c0 (T.fund a Z) h0p hp0
              rw [heq] at hGc0
              exact hGc0
            | inr heq =>
              rw [heq] at hGc0
              exact T.GBound_fund_one u a k hadom hGc0
        | ω => rw [hadom] at hd; cases hd
        | Ω m =>
          rw [hadom] at hd hlo
          cases hd
          cases c with
          | Z =>
            cases hlo with
            | inl hlt => exact False.elim (lt_Z_inv _ hlt)
            | inr heq => cases heq
          | P c0 c1 c2 =>
            have hlow := T.first_le_of_P_le (T.fund a (P (T.fund l Z) q Z)) Z Z c0 c1 c2 hlo
            have hhigh := T.first_le_of_P_le c0 c1 c2 a Z Z hhi
            have huf : u ≤ T.fund a (P (T.fund l Z) q Z) :=
              partial_order.trans u (P (T.fund l Z) q Z) _
                (Or.inl (lt_of_le_of_lt_thm T u (T.fund l Z) _ hup (T.first_lt _ q Z)))
                (T.input_le_fund_omega a l ha hadom _ (T.lt.p_first _ _ _ _ _ _ hlp))
            have huc := partial_order.trans u _ c0 huf hlow
            exact ih0 l c0 hadom hul hlow hhigh
              ((((T.GBound_P u c0 c1 c2 k).mp hG).1 huc).2.1)
      | One => rw [hbdom] at hd; cases hd
      | ω => rw [hbdom] at hd; cases hd
      | Ω m =>
        rw [hbdom] at hd hlo
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham] at hd
          cases hd
          change (if a < l then P a (T.fund b (T.iter
            (fun x => P (T.fund l Z) (T.fund b x) Z) (P (T.fund l Z) q Z))) Z
            else P a (T.fund b (P (T.fund l Z) q Z)) Z) ≤ c at hlo
          rw [ite_eq_right ham] at hlo
          cases c with
          | Z =>
            cases hlo with
            | inl hlt => exact False.elim (lt_Z_inv _ hlt)
            | inr heq => cases heq
          | P c0 c1 c2 =>
            have heq := partial_order.antisymm c0 a
              (T.first_le_of_P_le c0 c1 c2 a b Z hhi)
              (T.first_le_of_P_le a _ Z c0 c1 c2 hlo)
            cases heq
            have hlow := T.second_le_of_P_le a _ Z c1 c2 hlo
            have hhigh := T.second_le_of_P_le a c1 c2 b Z hhi
            have hua : u ≤ a := Or.inl (lt_of_lt_of_le_thm T u l a hul (T.le_of_not_lt a l ham))
            exact ih1 l c1 hbdom hul hlow hhigh
              ((((T.GBound_P u a c1 c2 k).mp hG).1 hua).2.2)
    · rw [T.dom, ite_eq_right hdZ] at hd
      rw [T.fund, ite_eq_right hdZ] at hlo
      cases c with
      | Z =>
        cases hlo with
        | inl hlt => exact False.elim (lt_Z_inv _ hlt)
        | inr heq => cases heq
      | P c0 c1 c2 =>
        have h0 := partial_order.antisymm c0 a
          (T.first_le_of_P_le c0 c1 c2 a b d hhi) (T.first_le_of_P_le a b _ c0 c1 c2 hlo)
        cases h0
        have h1 := partial_order.antisymm c1 b
          (T.second_le_of_P_le a c1 c2 b d hhi) (T.second_le_of_P_le a b _ c1 c2 hlo)
        cases h1
        exact ih2 l c2 hd hul (T.third_le_of_P_le a b _ c2 hlo)
          (T.third_le_of_P_le a b c2 d hhi) ((T.GBound_P u a b c2 k).mp hG).2

theorem T.fund_collapsing_principal_supportStep (a b l : T) (hs : T.isNF (P a b Z))
    (hd : T.dom b = .Ω l) (hal : a < l) (n : Nat) :
    T.SupportStep (T.ofNat n) (T.fund (P a b Z) (T.ofNat n)) (P a b Z) := by
  have hb := (T.isNF_components a b Z hs).2.1
  let F := fun x => P (T.fund l Z) (T.fund b x) Z
  let xs := fun m => T.iter F (T.ofNat m)
  let bs := fun m => T.fund b (xs m)
  have hlone := T.dom_omega_index_one b l hd
  have hlne : l ≠ Z := by intro heq; rw [heq] at hlone; cases hlone
  have hlp := T.fund_lt_of_domain l Z hlne (fun m _ => T.lt.Z_lt_P m Z Z)
  have hxs : ∀ m, xs m < P l Z Z := by
    intro m
    cases m with
    | zero => exact T.lt.Z_lt_P l Z Z
    | succ m => exact T.lt.p_first _ _ _ _ _ _ hlp
  have hbs : ∀ m, bs m < bs (m + 1) := T.collapsing_iterates_strict b l hd
  have heq : T.fund (P a b Z) (T.ofNat n) = P a (bs n) Z := by
    rw [T.fund, ite_eq_left rfl, hd]
    change (if a < l then _ else _) = _
    rw [ite_eq_left hal]
  refine ⟨T.fund_ofNat_lt (P a b Z) n (by intro h; cases h), ?_⟩
  intro u c k hlo hhi hG hz hk
  rw [heq] at hlo ⊢
  cases c with
  | Z =>
    cases hlo with
    | inl hlt => exact False.elim (lt_Z_inv _ hlt)
    | inr heq => cases heq
  | P c0 c1 c2 =>
    have h0 := partial_order.antisymm c0 a
      (T.first_le_of_P_le c0 c1 c2 a b Z hhi) (T.first_le_of_P_le a (bs n) Z c0 c1 c2 hlo)
    cases h0
    have hlow := T.second_le_of_P_le a (bs n) Z c1 c2 hlo
    have hhigh := T.second_le_of_P_le a c1 c2 b Z hhi
    apply (T.GBound_P u a (bs n) Z k).mpr
    refine ⟨?_, T.GBound_zero u k⟩
    intro hua
    have hul := lt_of_le_of_lt_thm T u a l hua hal
    have hp := ((T.GBound_P u a c1 c2 k).mp hG).1 hua
    have hcontrol : ∀ m, bs m ≤ c1 → T.GBound u (xs m) k ∧ T.GBound u (bs m) k := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hzero := T.GBound_zero u k
        exact ⟨hzero, (T.fund_omega_supportStep b l Z hd (hxs 0)).2
          u c1 k hm hhigh hp.2.2 hzero hk⟩
      | succ m ih =>
        intro hm
        have hprev : bs m ≤ c1 := Or.inl (lt_of_lt_of_le_thm T (bs m) (bs (m + 1)) c1 (hbs m) hm)
        have hprevG := (ih hprev).2
        have hindex := T.GBound_predecessor_of_fund_interval b hb l u (bs m) c1 k
          hd hul hm hhigh hp.2.2
        have hinput : T.GBound u (xs (m + 1)) k := by
          apply (T.GBound_P u (T.fund l Z) (bs m) Z k).mpr
          exact ⟨fun _ => ⟨lt_of_le_of_lt_thm T (bs m) c1 k hprev hp.1, hindex, hprevG⟩,
            T.GBound_zero u k⟩
        exact ⟨hinput, (T.fund_omega_supportStep b l (xs (m + 1)) hd (hxs (m + 1))).2
          u c1 k hm hhigh hp.2.2 hinput hk⟩
    exact ⟨lt_of_le_of_lt_thm T (bs n) c1 k hlow hp.1, hp.2.1, (hcontrol n hlow).2⟩

theorem T.fund_one_supportStep (s : T) (hd : T.dom s = .One) :
    T.SupportStep Z (T.fund s Z) s := by
  have hs : s ≠ Z := by intro heq; rw [heq] at hd; cases hd
  refine ⟨T.fund_lt_of_domain s Z hs (fun l _ => T.lt.Z_lt_P l Z Z), ?_⟩
  intro u c k hlo hhi hG hz hk
  cases hhi with
  | inr heq => rw [heq] at hG; exact T.GBound_fund_one u s k hd hG
  | inl hlt =>
    have hback := (T.fund_one_properties s hd).2.2.1 c hlt
    have heq := partial_order.antisymm c (T.fund s Z) hback hlo
    rw [heq] at hG
    exact hG

theorem T.fund_principal_successor_supportStep (a b : T) (hd : T.dom b = .One) (n : Nat) :
    T.SupportStep (T.ofNat n) (T.fund (P a b Z) (T.ofNat n)) (P a b Z) := by
  have hA := (T.fund_one_supportStep b hd).principal a
  have heq : T.fund (P a b Z) (T.ofNat n) = T.mul (P a (T.fund b Z) Z) (T.ofNat n) := by
    rw [T.fund, ite_eq_left rfl, hd]
  refine ⟨T.fund_ofNat_lt (P a b Z) n (by intro h; cases h), ?_⟩
  intro u c k hlo hhi hG hz hk
  rw [heq] at hlo ⊢
  cases n with
  | zero => exact T.GBound_zero u k
  | succ n =>
    apply T.GBound_mul_principal
    have hhead : P a (T.fund b Z) Z ≤ T.mul (P a (T.fund b Z) Z) (T.ofNat (n + 1)) := by
      rw [T.mul_principal_ofNat_succ]
      exact T.head_le (P a (T.fund b Z) (T.mul (P a (T.fund b Z) Z) (T.ofNat n)))
    exact hA.2 u c k (partial_order.trans _ _ _ hhead hlo) hhi hG (T.GBound_zero u k) hk

theorem T.fund_ofNat_supportStep (s : T) (hs : T.isNF s) (hne : s ≠ Z) (n : Nat) :
    T.SupportStep (T.ofNat n) (T.fund s (T.ofNat n)) s := by
  induction hs with
  | z => exact False.elim (hne rfl)
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hs := T.isNF.p a b c ha hb hc hreg hhead
    by_cases hcZ : c = Z
    · cases hcZ
      cases hbdom : T.dom b with
      | Zero =>
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        rw [T.fund, ite_eq_left rfl, hbdom]
        cases hadom : T.dom a with
        | Zero => exact T.SupportStep.zero (T.ofNat n) (P a Z Z) (T.lt.Z_lt_P a Z Z)
        | One =>
          have hane : a ≠ Z := by intro heq; rw [heq] at hadom; cases hadom
          exact T.SupportStep.input (T.ofNat n) (P a Z Z) (T.ofNat_lt_index n a hane)
        | ω =>
          have hane : a ≠ Z := by intro heq; rw [heq] at hadom; cases hadom
          exact (ih0 hane).index
        | Ω l =>
          have hane : a ≠ Z := by intro heq; rw [heq] at hadom; cases hadom
          exact (ih0 hane).index
      | One => exact T.fund_principal_successor_supportStep a b hbdom n
      | ω =>
        rw [T.fund, ite_eq_left rfl, hbdom]
        have hbne : b ≠ Z := by intro heq; rw [heq] at hbdom; cases hbdom
        exact (ih1 hbne).principal a
      | Ω l =>
        by_cases hal : a < l
        · exact T.fund_collapsing_principal_supportStep a b l hs hbdom hal n
        · rw [T.fund, ite_eq_left rfl, hbdom]
          change T.SupportStep (T.ofNat n) (if a < l then _ else _) (P a b Z)
          rw [ite_eq_right hal]
          have hbne : b ≠ Z := by intro heq; rw [heq] at hbdom; cases hbdom
          exact (ih1 hbne).principal a
    · rw [T.fund, ite_eq_right hcZ]
      exact (ih2 hcZ).tail a b

theorem T.fund_ofNat_regular (s u : T) (hs : T.isNF s) (hG : T.GBound u s s) (n : Nat) :
    T.GBound u (T.fund s (T.ofNat n)) (T.fund s (T.ofNat n)) := by
  by_cases hsZ : s = Z
  · rw [hsZ, T.fund_Z]
    exact T.GBound_zero u Z
  · by_cases hrZ : T.fund s (T.ofNat n) = Z
    · rw [hrZ]
      exact T.GBound_zero u Z
    · apply (T.fund_ofNat_supportStep s hs hsZ n).regular u hG
      intro x hx
      have heq := (T.mem_G_ofNat u n x hx).1
      rw [heq]
      cases he : T.fund s (T.ofNat n) with
      | Z => exact False.elim (hrZ he)
      | P a b c => exact T.lt.Z_lt_P a b c

theorem T.fund_ofNat_isNF (s : T) (hs : T.isNF s) (n : Nat) :
    T.isNF (T.fund s (T.ofNat n)) := by
  induction hs with
  | z => rw [T.fund_Z]; exact T.isNF.z
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hs := T.isNF.p a b c ha hb hc hreg hhead
    by_cases hcZ : c = Z
    · cases hcZ
      cases hbdom : T.dom b with
      | Zero =>
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        rw [T.fund, ite_eq_left rfl, hbdom]
        cases hadom : T.dom a with
        | Zero => exact T.isNF.z
        | One => exact T.ofNat_isNF n
        | ω => exact T.isNF_index (T.fund a (T.ofNat n)) ih0
        | Ω l => exact T.isNF_index (T.fund a (T.ofNat n)) ih0
      | One => exact T.fund_principal_successor_isNF a b (T.ofNat n) hs hbdom
      | ω =>
        rw [T.fund, ite_eq_left rfl, hbdom]
        exact T.isNF.p a (T.fund b (T.ofNat n)) Z ha ih1 T.isNF.z
          (T.fund_ofNat_regular b a hb hreg n) (T.Z_le _)
      | Ω l =>
        by_cases hal : a < l
        · exact T.fund_collapsing_principal_isNF a b l hs hbdom hal n
        · rw [T.fund, ite_eq_left rfl, hbdom]
          change T.isNF (if a < l then _ else _)
          rw [ite_eq_right hal]
          exact T.isNF.p a (T.fund b (T.ofNat n)) Z ha ih1 T.isNF.z
            (T.fund_ofNat_regular b a hb hreg n) (T.Z_le _)
    · exact T.fund_nonzero_tail_isNF a b c (T.ofNat n) hs hcZ ih2 (T.ofNat_in_domain c n)
