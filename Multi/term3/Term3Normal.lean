import Multi.term3.Term3Fundamental

open T

def T.head : T → T
  | Z => Z
  | P a b c _ => P a b c Z

/-- Support for the first collapsing level. The third coordinate belongs to
the lower collapsing level and is not unfolded here. -/
def T.G₁ (u : T) : T → List T
  | Z => []
  | P a b _ d =>
    if u ≤ a then [b] ++ T.G₁ u a ++ T.G₁ u b ++ T.G₁ u d else T.G₁ u d

/-- Support for the second collapsing level. -/
def T.G₂ (u v : T) : T → List T
  | Z => []
  | P a b c d =>
    if P u v Z Z ≤ P a b Z Z then
      [b, c] ++ T.G₂ u v a ++ T.G₂ u v b ++ T.G₂ u v c ++ T.G₂ u v d
    else T.G₂ u v d

inductive T.isNF : T → Prop where
  | z : T.isNF Z
  | p (a b c d : T) (ha : T.isNF a) (hb : T.isNF b) (hc : T.isNF c) (hd : T.isNF d)
      (h₁ : ∀ x, x ∈ T.G₁ a b → x < b)
      (h₂ : ∀ x, x ∈ T.G₂ a b c → x < c)
      (hhead : T.head d ≤ P a b c Z) : T.isNF (P a b c d)

def T.NF := { s : T // T.isNF s }

theorem T.isNF_components (a b c d : T) (h : T.isNF (P a b c d)) :
    T.isNF a ∧ T.isNF b ∧ T.isNF c ∧ T.isNF d := by
  cases h with
  | p _ _ _ _ ha hb hc hd _ _ _ => exact ⟨ha, hb, hc, hd⟩

theorem T.head_isNF (s : T) (hs : T.isNF s) : T.isNF (T.head s) := by
  cases hs with
  | z => exact T.isNF.z
  | p a b c d ha hb hc hd h₁ h₂ hhead =>
    exact T.isNF.p a b c Z ha hb hc T.isNF.z h₁ h₂ (T.Z_le _)

theorem T.isNF_index (a : T) (ha : T.isNF a) : T.isNF (P a Z Z Z) := by
  apply T.isNF.p a Z Z Z ha T.isNF.z T.isNF.z T.isNF.z
  · intro x hx; exact False.elim (List.not_mem_nil hx)
  · intro x hx; exact False.elim (List.not_mem_nil hx)
  · exact T.Z_le _

theorem T.G₁_P_of_le (u a b c d : T) (h : u ≤ a) :
    T.G₁ u (P a b c d) = [b] ++ T.G₁ u a ++ T.G₁ u b ++ T.G₁ u d := by
  rw [T.G₁, ite_eq_left h]

theorem T.G₁_P_of_not_le (u a b c d : T) (h : ¬ u ≤ a) :
    T.G₁ u (P a b c d) = T.G₁ u d := by
  rw [T.G₁, ite_eq_right h]

theorem T.G₂_P_of_le (u v a b c d : T) (h : P u v Z Z ≤ P a b Z Z) :
    T.G₂ u v (P a b c d) =
      [b, c] ++ T.G₂ u v a ++ T.G₂ u v b ++ T.G₂ u v c ++ T.G₂ u v d := by
  rw [T.G₂, ite_eq_left h]

theorem T.G₂_P_of_not_le (u v a b c d : T) (h : ¬ P u v Z Z ≤ P a b Z Z) :
    T.G₂ u v (P a b c d) = T.G₂ u v d := by
  rw [T.G₂, ite_eq_right h]

theorem T.mem_G₁_properties (u s x : T) (hs : T.isNF s) (hx : x ∈ T.G₁ u s) :
    T.isNF x ∧ T.size x < T.size s := by
  induction hs with
  | z => exact False.elim (List.not_mem_nil hx)
  | p a b c d ha hb hc hd h₁ h₂ hhead ih0 ih1 ih2 ih3 =>
    by_cases hua : u ≤ a
    · rw [T.G₁_P_of_le u a b c d hua] at hx
      cases List.mem_append.mp hx with
      | inr hx =>
        have hp := ih3 hx
        exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_fourth _ _ _ _)⟩
      | inl hx =>
        cases List.mem_append.mp hx with
        | inr hx =>
          have hp := ih1 hx
          exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_second _ _ _ _)⟩
        | inl hx =>
          cases List.mem_append.mp hx with
          | inr hx =>
            have hp := ih0 hx
            exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_first _ _ _ _)⟩
          | inl hx =>
            have heq := List.mem_singleton.mp hx
            cases heq
            exact ⟨hb, T.size_lt_size_P_second _ _ _ _⟩
    · rw [T.G₁_P_of_not_le u a b c d hua] at hx
      have hp := ih3 hx
      exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_fourth _ _ _ _)⟩

theorem T.mem_G₂_properties (u v s x : T) (hs : T.isNF s) (hx : x ∈ T.G₂ u v s) :
    T.isNF x ∧ T.size x < T.size s := by
  induction hs with
  | z => exact False.elim (List.not_mem_nil hx)
  | p a b c d ha hb hc hd h₁ h₂ hhead ih0 ih1 ih2 ih3 =>
    by_cases huv : P u v Z Z ≤ P a b Z Z
    · rw [T.G₂_P_of_le u v a b c d huv] at hx
      cases List.mem_append.mp hx with
      | inr hx =>
        have hp := ih3 hx
        exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_fourth _ _ _ _)⟩
      | inl hx =>
        cases List.mem_append.mp hx with
        | inr hx =>
          have hp := ih2 hx
          exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_third _ _ _ _)⟩
        | inl hx =>
          cases List.mem_append.mp hx with
          | inr hx =>
            have hp := ih1 hx
            exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_second _ _ _ _)⟩
          | inl hx =>
            cases List.mem_append.mp hx with
            | inr hx =>
              have hp := ih0 hx
              exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_first _ _ _ _)⟩
            | inl hx =>
              cases List.mem_cons.mp hx with
              | inl heq =>
                cases heq
                exact ⟨hb, T.size_lt_size_P_second _ _ _ _⟩
              | inr hx =>
                have heq := List.mem_singleton.mp hx
                cases heq
                exact ⟨hc, T.size_lt_size_P_third _ _ _ _⟩
    · rw [T.G₂_P_of_not_le u v a b c d huv] at hx
      have hp := ih3 hx
      exact ⟨hp.1, Nat.lt_trans hp.2 (T.size_lt_size_P_fourth _ _ _ _)⟩

theorem T.LF_isNF (n : Nat) : T.isNF (T.LF n) := by
  induction n with
  | zero => exact T.isNF.z
  | succ n ih => exact T.isNF_index (T.LF n) ih

theorem T.ofNat_head_le_one (n : Nat) : T.head (T.ofNat n) ≤ P Z Z Z Z := by
  cases n with
  | zero => exact T.Z_le _
  | succ n => exact Or.inr rfl

theorem T.ofNat_isNF (n : Nat) : T.isNF (T.ofNat n) := by
  induction n with
  | zero => exact T.isNF.z
  | succ n ih =>
    apply T.isNF.p Z Z Z (T.ofNat n) T.isNF.z T.isNF.z T.isNF.z ih
    · intro x hx; exact False.elim (List.not_mem_nil hx)
    · intro x hx; exact False.elim (List.not_mem_nil hx)
    · exact T.ofNat_head_le_one n

theorem T.mem_G₂_LF (u v : T) (n : Nat) (x : T) (hx : x ∈ T.G₂ u v (T.LF n)) : x = Z := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hx)
  | succ n ih =>
    change x ∈ T.G₂ u v (P (T.LF n) Z Z Z) at hx
    by_cases hle : P u v Z Z ≤ P (T.LF n) Z Z Z
    · rw [T.G₂_P_of_le u v (T.LF n) Z Z Z hle] at hx
      cases List.mem_append.mp hx with
      | inr hx => exact False.elim (List.not_mem_nil hx)
      | inl hx =>
        cases List.mem_append.mp hx with
        | inr hx => exact False.elim (List.not_mem_nil hx)
        | inl hx =>
          cases List.mem_append.mp hx with
          | inr hx => exact False.elim (List.not_mem_nil hx)
          | inl hx =>
            cases List.mem_append.mp hx with
            | inr hx => exact ih hx
            | inl hx =>
              cases List.mem_cons.mp hx with
              | inl heq => exact heq
              | inr hx => exact List.mem_singleton.mp hx
    · rw [T.G₂_P_of_not_le u v (T.LF n) Z Z Z hle] at hx
      exact False.elim (List.not_mem_nil hx)

theorem T.base_isNF (n : Nat) : T.isNF (P Z Z (T.LF n) Z) := by
  apply T.isNF.p Z Z (T.LF n) Z T.isNF.z T.isNF.z (T.LF_isNF n) T.isNF.z
  · intro x hx; exact False.elim (List.not_mem_nil hx)
  · intro x hx
    have heq := T.mem_G₂_LF Z Z n x hx
    rw [heq]
    cases n with
    | zero => exact False.elim (List.not_mem_nil hx)
    | succ n => exact T.lt.Z_lt_P _ _ _ _
  · exact T.Z_le _

theorem T.head_le (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P a b c d =>
    cases d with
    | Z => exact Or.inr rfl
    | P d0 d1 d2 d3 => exact Or.inl (T.lt.p_fourth _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))

theorem T.first_lt (a b c d : T) : a < P a b c d := by
  induction a generalizing b c d with
  | Z => exact T.lt.Z_lt_P _ _ _ _
  | P a0 a1 a2 a3 ih0 ih1 ih2 ih3 =>
    exact T.lt.p_first _ _ _ _ _ _ _ _ (ih0 a1 a2 a3)

theorem T.le_of_not_lt (a b : T) (h : ¬ a < b) : b ≤ a := by
  cases T.lt_total a b with
  | inl hab => exact False.elim (h hab)
  | inr hrest =>
    cases hrest with
    | inl hba => exact Or.inl hba
    | inr heq => exact Or.inr heq.symm

theorem T.dom_omega_properties (s : T) (hs : T.isNF s) (l0 l1 : T)
    (hd : T.dom s = .Ω l0 l1) :
    T.isNF (P l0 l1 Z Z) ∧ P l0 l1 Z Z ≤ T.head s := by
  induction hs generalizing l0 l1 with
  | z => cases hd
  | p a b c d ha hb hc hdNF h₁ h₂ hhead ih0 ih1 ih2 ih3 =>
    by_cases hdZ : d = Z
    · cases hdZ
      rw [T.dom, ite_eq_left rfl] at hd
      cases hcD : T.dom c with
      | Zero =>
        have hcZ := T.dom_eq_zero c hcD
        cases hcZ
        rw [hcD] at hd
        cases hbD : T.dom b with
        | Zero =>
          have hbZ := T.dom_eq_zero b hbD
          cases hbZ
          rw [hbD] at hd
          cases haD : T.dom a with
          | Zero => rw [haD] at hd; cases hd
          | One => rw [haD] at hd; cases hd; exact ⟨T.isNF_index a ha, Or.inr rfl⟩
          | ω => rw [haD] at hd; cases hd
          | Ω m0 m1 =>
            rw [haD] at hd
            cases hd
            have hp := ih0 l0 l1 haD
            exact ⟨hp.1, Or.inl (lt_of_le_of_lt_thm T _ a _
              (partial_order.trans _ _ _ hp.2 (T.head_le a)) (T.first_lt a Z Z Z))⟩
        | One =>
          rw [hbD] at hd
          cases hd
          have hnf : T.isNF (P a b Z Z) :=
            T.isNF.p a b Z Z ha hb T.isNF.z T.isNF.z h₁ h₂ (T.Z_le _)
          exact ⟨hnf, Or.inr rfl⟩
        | ω => rw [hbD] at hd; cases hd
        | Ω m0 m1 =>
          rw [hbD] at hd
          change (if P a b Z Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) = Dom.Ω l0 l1 at hd
          by_cases hlt : P a b Z Z < P m0 m1 Z Z
          · rw [ite_eq_left hlt] at hd; cases hd
          · rw [ite_eq_right hlt] at hd
            cases hd
            exact ⟨(ih1 l0 l1 hbD).1, T.le_of_not_lt _ _ hlt⟩
      | One => rw [hcD] at hd; cases hd
      | ω => rw [hcD] at hd; cases hd
      | Ω m0 m1 =>
        rw [hcD] at hd
        change (if P a b c Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) = Dom.Ω l0 l1 at hd
        by_cases hlt : P a b c Z < P m0 m1 Z Z
        · rw [ite_eq_left hlt] at hd; cases hd
        · rw [ite_eq_right hlt] at hd
          cases hd
          exact ⟨(ih2 l0 l1 hcD).1, T.le_of_not_lt _ _ hlt⟩
    · rw [T.dom, ite_eq_right hdZ] at hd
      have hp := ih3 l0 l1 hd
      exact ⟨hp.1, partial_order.trans _ _ _ hp.2 hhead⟩

theorem T.first_uncountable_le_domain (s l0 l1 : T) (hd : T.dom s = .Ω l0 l1) :
    P Z (P Z Z Z Z) Z Z ≤ P l0 l1 Z Z := by
  cases l0 with
  | P a b c d => exact Or.inl (T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))
  | Z =>
    have hl1 : T.dom l1 = .One := by
      cases T.dom_omega_index_cases s Z l1 hd with
      | inl h => exact h
      | inr h => cases h.2
    cases l1 with
    | Z => cases hl1
    | P a b c d =>
      have hone : P Z Z Z Z ≤ P a b c d := by
        cases a with
        | P a0 a1 a2 a3 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))
        | Z =>
          cases b with
          | P b0 b1 b2 b3 => exact Or.inl (T.lt.p_second _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))
          | Z =>
            cases c with
            | P c0 c1 c2 c3 => exact Or.inl (T.lt.p_third _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))
            | Z =>
              cases d with
              | P d0 d1 d2 d3 => exact Or.inl (T.lt.p_fourth _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _))
              | Z => exact Or.inr rfl
      cases hone with
      | inl h => exact Or.inl (T.lt.p_second _ _ _ _ _ _ _ h)
      | inr h => rw [← h]; exact Or.inr rfl

theorem T.dom_ne_omega_below_first_uncountable (s : T) (hs : T.isNF s)
    (hbound : s < P Z (P Z Z Z Z) Z Z) : ∀ l0 l1, T.dom s ≠ .Ω l0 l1 := by
  intro l0 l1 hd
  have hp := T.dom_omega_properties s hs l0 l1 hd
  have hle : P Z (P Z Z Z Z) Z Z ≤ s :=
    partial_order.trans _ _ _ (T.first_uncountable_le_domain s l0 l1 hd)
      (partial_order.trans _ _ _ hp.2 (T.head_le s))
  exact T.lt_irrefl s (lt_of_lt_of_le_thm T _ _ _ hbound hle)
