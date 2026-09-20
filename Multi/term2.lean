import Multi.order
import Multi.OCF.Hierarchy

inductive T where
| Z
| P (s0 s1 s2 : T)
deriving DecidableEq

open T

inductive T.lt : T → T → Prop where
| Z_lt_P (t0 t1 t2 : T) :
  T.lt Z (P t0 t1 t2)
| p_first (s0 s1 s2 t0 t1 t2 : T) (h : T.lt s0 t0) :
  T.lt (P s0 s1 s2) (P t0 t1 t2)
| p_second (s0 s1 s2 t1 t2 : T) (h : T.lt s1 t1) :
  T.lt (P s0 s1 s2) (P s0 t1 t2)
| p_third (s0 s1 s2 t2 : T) (h : T.lt s2 t2) :
  T.lt (P s0 s1 s2) (P s0 s1 t2)

instance : LT T where
  lt a b := T.lt a b

theorem lt_Z_Z_inv (h : Z < Z) : False := by
  cases h

theorem lt_P_Z_inv (s0 s1 s2 : T) (h : (P s0 s1 s2) < Z) : False := by
  cases h

theorem lt_Z_inv (a : T) (h : a < Z) : False := by
  cases a with
  | Z => exact lt_Z_Z_inv h
  | P a0 a1 a2 => exact lt_P_Z_inv a0 a1 a2 h

theorem lt_inv (s0 s1 s2 t0 t1 t2 : T) (h : P s0 s1 s2 < P t0 t1 t2) :
  s0 < t0 ∨ (s0 = t0 ∧ s1 < t1) ∨ (s0 = t0 ∧ s1 = t1 ∧ s2 < t2) := by
  cases h
  case p_first h_lt =>
    apply Or.inl
    exact h_lt
  case p_second h_lt =>
    apply Or.inr
    apply Or.inl
    apply And.intro
    · rfl
    · exact h_lt
  case p_third h_lt =>
    apply Or.inr
    apply Or.inr
    apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · exact h_lt

def T.decLt (a b : T) : Decidable (a < b) :=
  match a, b with
  | Z, Z => isFalse lt_Z_Z_inv
  | Z, P t0 t1 t2 => isTrue (T.lt.Z_lt_P t0 t1 t2)
  | P s0 s1 s2, Z => isFalse (lt_P_Z_inv s0 s1 s2)
  | P s0 s1 s2, P t0 t1 t2 =>
    match T.decLt s0 t0 with
    | isTrue h0 => isTrue (T.lt.p_first s0 s1 s2 t0 t1 t2 h0)
    | isFalse hn0 =>
      if heq0 : s0 = t0 then
        match t0, heq0 with
        | _, rfl =>
          match T.decLt s1 t1 with
          | isTrue h1 => isTrue (T.lt.p_second s0 s1 s2 t1 t2 h1)
          | isFalse hn1 =>
            if heq1 : s1 = t1 then
              match t1, heq1 with
              | _, rfl =>
                match T.decLt s2 t2 with
                | isTrue h2 => isTrue (T.lt.p_third s0 s1 s2 t2 h2)
                | isFalse hn2 =>
                  isFalse (fun h =>
                      match lt_inv s0 s1 s2 s0 s1 t2 h with
                      | Or.inl h_lt => hn0 h_lt
                      | Or.inr (Or.inl h_and) => hn1 h_and.2
                      | Or.inr (Or.inr h_and) => hn2 h_and.2.2
                    )
            else
              isFalse (fun h =>
                match lt_inv s0 s1 s2 s0 t1 t2 h with
                | Or.inl h_lt => hn0 h_lt
                | Or.inr (Or.inl h_and) => hn1 h_and.2
                | Or.inr (Or.inr h_and) => heq1 h_and.2.1
              )
      else
        isFalse (fun h =>
          match lt_inv s0 s1 s2 t0 t1 t2 h with
          | Or.inl h_lt => hn0 h_lt
          | Or.inr (Or.inl h_and) => heq0 h_and.1
          | Or.inr (Or.inr h_and) => heq0 h_and.1
        )

instance (a b : T) : Decidable (a < b) :=
  T.decLt a b

theorem T.lt_irrefl (a : T) : ¬ a < a := by
  induction a with
  | Z =>
    intro h
    exact lt_Z_Z_inv h
  | P s0 s1 s2 ih0 ih1 ih2 =>
    intro h
    have h_inv := lt_inv s0 s1 s2 s0 s1 s2 h
    cases h_inv with
    | inl h_lt =>
      exact ih0 h_lt
    | inr h_or0 =>
      cases h_or0 with
      | inl h_lt =>
        exact ih1 h_lt.2
      | inr h_and =>
        exact ih2 h_and.2.2

theorem T.lt_trans (a : T) : ∀ b c : T, a < b → b < c → a < c := by
  induction a with
  | Z =>
    intro b c hab hbc
    cases c with
    | Z => exact False.elim (lt_Z_inv b hbc)
    | P c0 c1 c2 => exact T.lt.Z_lt_P c0 c1 c2
  | P a0 a1 a2 ih0 ih1 ih2 =>
    intro b c hab hbc
    cases b with
    | Z => exact False.elim (lt_P_Z_inv a0 a1 a2 hab)
    | P b0 b1 b2 =>
      cases c with
      | Z => exact False.elim (lt_P_Z_inv b0 b1 b2 hbc)
      | P c0 c1 c2 =>
        cases hab with
        | p_first _ _ _ _ _ _ hab0 =>
          cases hbc with
          | p_first _ _ _ _ _ _ hbc0 =>
            exact T.lt.p_first _ _ _ _ _ _ (ih0 _ _ hab0 hbc0)
          | p_second _ _ _ _ _ hbc1 => exact T.lt.p_first _ _ _ _ _ _ hab0
          | p_third _ _ _ _ hbc2 => exact T.lt.p_first _ _ _ _ _ _ hab0
        | p_second _ _ _ _ _ hab1 =>
          cases hbc with
          | p_first _ _ _ _ _ _ hbc0 => exact T.lt.p_first _ _ _ _ _ _ hbc0
          | p_second _ _ _ _ _ hbc1 =>
            exact T.lt.p_second _ _ _ _ _ (ih1 _ _ hab1 hbc1)
          | p_third _ _ _ _ hbc2 => exact T.lt.p_second _ _ _ _ _ hab1
        | p_third _ _ _ _ hab2 =>
          cases hbc with
          | p_first _ _ _ _ _ _ hbc0 => exact T.lt.p_first _ _ _ _ _ _ hbc0
          | p_second _ _ _ _ _ hbc1 => exact T.lt.p_second _ _ _ _ _ hbc1
          | p_third _ _ _ _ hbc2 =>
            exact T.lt.p_third _ _ _ _ (ih2 _ _ hab2 hbc2)

theorem T.lt_asymm {a b : T} (h : a < b) : ¬ (b < a) := by
  intro hba
  have htrans := T.lt_trans a b a h hba
  exact T.lt_irrefl a htrans

theorem T.lt_total (a b : T) : a < b ∨ b < a ∨ a = b := by
  induction a generalizing b with
  | Z =>
    cases b with
    | Z => exact Or.inr (Or.inr rfl)
    | P b0 b1 b2 => exact Or.inl (T.lt.Z_lt_P b0 b1 b2)
  | P a0 a1 a2 ih0 ih1 ih2 =>
    cases b with
    | Z => exact Or.inr (Or.inl (T.lt.Z_lt_P a0 a1 a2))
    | P b0 b1 b2 =>
      cases ih0 b0 with
      | inl h0 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
      | inr h0 =>
        cases h0 with
        | inl h0 => exact Or.inr (Or.inl (T.lt.p_first _ _ _ _ _ _ h0))
        | inr e0 =>
          cases e0
          cases ih1 b1 with
          | inl h1 => exact Or.inl (T.lt.p_second _ _ _ _ _ h1)
          | inr h1 =>
            cases h1 with
            | inl h1 => exact Or.inr (Or.inl (T.lt.p_second _ _ _ _ _ h1))
            | inr e1 =>
              cases e1
              cases ih2 b2 with
              | inl h2 => exact Or.inl (T.lt.p_third _ _ _ _ h2)
              | inr h2 =>
                cases h2 with
                | inl h2 => exact Or.inr (Or.inl (T.lt.p_third _ _ _ _ h2))
                | inr e2 =>
                  cases e2
                  exact Or.inr (Or.inr rfl)

instance : strict_partial_order T where
  irrefl a := T.lt_irrefl a
  trans a b c hf hs := T.lt_trans a b c hf hs

instance : strict_linear_order T where
  total a b := T.lt_total a b

theorem T.Z_le (s : T) : Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P s0 s1 s2 =>
    apply Or.inl
    exact T.lt.Z_lt_P s0 s1 s2

def T.add : T → T → T
| Z, t => t
| s, Z => s
| P s0 s1 s2, t =>
  P s0 s1 (s2.add t)

instance : Add T where
  add := T.add

def T.mul : T → T → T
| _, Z => Z
| a, P _ _ m2 => mul a m2 + a

def T.iter (F : T → T) : T → T
| Z => Z
| P _ _ m2 => F (iter F m2)

def T.size : T → Nat
| Z => 0
| P t0 t1 t2 => t0.size + t1.size + t2.size + 1

theorem T.size_P (s0 s1 s2 : T) : (P s0 s1 s2).size = s0.size + s1.size + s2.size + 1 := rfl

theorem T.size_lt_size_P_first (s0 s1 s2 : T) : s0.size < (P s0 s1 s2).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  rw [Nat.add_assoc _ _ _]
  exact Nat.le_add_right _ _

theorem T.size_lt_size_P_second (s0 s1 s2 : T) : s1.size < (P s0 s1 s2).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  rw [Nat.add_comm s0.size s1.size]
  rw [Nat.add_assoc _ _ _]
  exact Nat.le_add_right _ _

theorem T.size_lt_size_P_third (s0 s1 s2 : T) : s2.size < (P s0 s1 s2).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  exact Nat.le_add_left _ _

inductive T.Dom where
| Zero
| One
| ω
| Ω (l0 : T)
deriving DecidableEq

def T.dom (s : T) : Dom :=
  match s with
  | Z => .Zero
  | P s0 s1 s2 =>
    if s2 = Z then
      match T.dom s1 with
      | .Zero =>
        match T.dom s0 with
        | .Zero => .One
        | .One => .Ω s0
        | .ω => .ω
        | .Ω l => .Ω l
      | .One => .ω
      | .ω => .ω
      | .Ω l =>
        if s0 < l then
          .ω
        else .Ω l
    else T.dom s2

theorem T.dom_omega_size (s l : T) (h : T.dom s = .Ω l) :
    l.size < s.size := by
  induction s generalizing l with
  | Z =>
    change Dom.Zero = Dom.Ω l at h
    cases h
  | P s0 s1 s2 ih0 ih1 ih2 =>
    rw [T.dom] at h
    split at h
    · cases h1 : T.dom s1 with
      | Zero =>
        rw [h1] at h
        cases h0 : T.dom s0 with
        | Zero =>
          rw [h0] at h
          cases h
        | One =>
          rw [h0] at h
          cases h
          exact T.size_lt_size_P_first s0 s1 s2
        | ω =>
          rw [h0] at h
          cases h
        | Ω m =>
          rw [h0] at h
          cases h
          exact Nat.lt_trans (ih0 _ h0) (T.size_lt_size_P_first s0 s1 s2)
      | One =>
        rw [h1] at h
        cases h
      | ω =>
        rw [h1] at h
        cases h
      | Ω m =>
        rw [h1] at h
        change (if s0 < m then Dom.ω else Dom.Ω m) = Dom.Ω l at h
        split at h
        · cases h
        · cases h
          exact Nat.lt_trans (ih1 _ h1) (T.size_lt_size_P_second s0 s1 s2)
    · exact Nat.lt_trans (ih2 l h) (T.size_lt_size_P_third s0 s1 s2)

def T.fund (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom s1 with
      | .Zero =>
        match _h0 : T.dom s0 with
        | .Zero => Z
        | .One => t
        | .ω => P (T.fund s0 t) Z Z
        | .Ω _ => P (T.fund s0 t) Z Z
      | .One => T.mul (P s0 (T.fund s1 Z) Z) t
      | .ω => P s0 (T.fund s1 t) Z
      | .Ω l =>
        if s0 < l then
          let l' := T.fund l Z
          let F := fun x => P l' (T.fund s1 x) Z
          P s0 (T.fund s1 (T.iter F t)) Z
        else P s0 (T.fund s1 t) Z
    else P s0 s1 (T.fund s2 t)
termination_by T.size s
decreasing_by
  · exact T.size_lt_size_P_first s0 s1 s2
  · exact T.size_lt_size_P_first s0 s1 s2
  · exact T.size_lt_size_P_second s0 s1 s2
  · exact T.size_lt_size_P_second s0 s1 s2
  · exact Nat.lt_trans (T.dom_omega_size s1 l _h1)
      (T.size_lt_size_P_second s0 s1 s2)
  · exact T.size_lt_size_P_second s0 s1 s2
  · exact T.size_lt_size_P_second s0 s1 s2
  · exact T.size_lt_size_P_second s0 s1 s2
  · exact T.size_lt_size_P_third s0 s1 s2

def T.head : T → T
| Z => Z
| P s0 s1 _ => P s0 s1 Z

def T.G (u s : T) : List T :=
  match s with
  | Z => []
  | P s0 s1 s2 =>
    let Gs0 := T.G u s0
    let Gs2 := T.G u s2
    if u ≤ s0 then
      [s1] ++ Gs0 ++ T.G u s1 ++ Gs2
    else Gs2

inductive T.isNF : T → Prop where
| z : T.isNF Z
| p (s0 s1 s2 : T) (hs1 : T.isNF s0) (hs1 : T.isNF s1) (hs2 : T.isNF s2)
  (h1 : ∀ x : T, x ∈ T.G s0 s1 → x < s1)
  (h2 : T.head s2 ≤ P s0 s1 Z) :
  T.isNF (P s0 s1 s2)

theorem T.isNF_components (s0 s1 s2 : T) (h : T.isNF (P s0 s1 s2)) :
    T.isNF s0 ∧ T.isNF s1 ∧ T.isNF s2 := by
  cases h with
  | p _ _ _ h0 h1 h2 _ _ => exact And.intro h0 (And.intro h1 h2)

theorem T.G_P_of_le (u s0 s1 s2 : T) (h : u ≤ s0) :
    T.G u (P s0 s1 s2) = [s1] ++ T.G u s0 ++ T.G u s1 ++ T.G u s2 := by
  rw [T.G, ite_eq_left h]

theorem T.G_P_of_not_le (u s0 s1 s2 : T) (h : ¬ u ≤ s0) :
    T.G u (P s0 s1 s2) = T.G u s2 := by
  rw [T.G, ite_eq_right h]

theorem T.isNF_index (s : T) (hs : T.isNF s) : T.isNF (P s Z Z) := by
  apply T.isNF.p s Z Z hs T.isNF.z T.isNF.z
  · intro x hx
    change x ∈ ([] : List T) at hx
    exact False.elim (List.not_mem_nil hx)
  · exact T.Z_le (P s Z Z)

theorem T.head_le (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P s0 s1 s2 =>
    cases s2 with
    | Z => exact Or.inr rfl
    | P t0 t1 t2 =>
      exact Or.inl (T.lt.p_third s0 s1 Z (P t0 t1 t2) (T.lt.Z_lt_P t0 t1 t2))

theorem T.first_lt (s0 s1 s2 : T) : s0 < P s0 s1 s2 := by
  induction s0 generalizing s1 s2 with
  | Z => exact T.lt.Z_lt_P Z s1 s2
  | P a0 a1 a2 ih0 _ _ =>
    exact T.lt.p_first _ _ _ _ _ _ (ih0 a1 a2)

theorem T.lt_one_inv (s : T) (h : s < P Z Z Z) : s = Z := by
  cases s with
  | Z => rfl
  | P s0 s1 s2 =>
    cases h with
    | p_first _ _ _ _ _ _ h0 => exact False.elim (lt_Z_inv _ h0)
    | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
    | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)

theorem T.below_omega_one_index (s0 s1 s2 : T)
    (h : P s0 s1 s2 < P (P Z Z Z) Z Z) : s0 = Z := by
  cases lt_inv s0 s1 s2 (P Z Z Z) Z Z h with
  | inl h0 => exact T.lt_one_inv s0 h0
  | inr hrest =>
    cases hrest with
    | inl h1 => exact False.elim (lt_Z_inv s1 h1.2)
    | inr h2 => exact False.elim (lt_Z_inv s2 h2.2.2)

theorem T.head_isNF (s : T) (hs : T.isNF s) : T.isNF (T.head s) := by
  cases hs with
  | z => exact T.isNF.z
  | p s0 s1 s2 h0 h1 h2 hG hhead =>
    exact T.isNF.p s0 s1 Z h0 h1 T.isNF.z hG (T.Z_le (P s0 s1 Z))

theorem T.head_size_le (s : T) : (T.head s).size ≤ s.size := by
  cases s with
  | Z => exact Nat.le_refl 0
  | P s0 s1 s2 =>
    change Nat.succ (s0.size + s1.size) ≤ Nat.succ (s0.size + s1.size + s2.size)
    exact Nat.succ_le_succ (Nat.le_add_right _ _)

theorem T.mem_G_properties (u s x : T) (hs : T.isNF s) (hx : x ∈ T.G u s) :
    T.isNF x ∧ x.size < s.size := by
  induction hs generalizing x with
  | z =>
    change x ∈ ([] : List T) at hx
    exact False.elim (List.not_mem_nil hx)
  | p s0 s1 s2 h0 h1 h2 hG hhead ih0 ih1 ih2 =>
    cases (inferInstance : Decidable (u ≤ s0)) with
    | isTrue hu =>
      rw [T.G_P_of_le u s0 s1 s2 hu] at hx
      cases List.mem_append.mp hx with
      | inr hx2 =>
        have hp := ih2 x hx2
        exact And.intro hp.1 (Nat.lt_trans hp.2 (T.size_lt_size_P_third s0 s1 s2))
      | inl hx01 =>
        cases List.mem_append.mp hx01 with
        | inr hx1 =>
          have hp := ih1 x hx1
          exact And.intro hp.1 (Nat.lt_trans hp.2 (T.size_lt_size_P_second s0 s1 s2))
        | inl hx0 =>
          cases List.mem_append.mp hx0 with
          | inr hx0 =>
            have hp := ih0 x hx0
            exact And.intro hp.1 (Nat.lt_trans hp.2 (T.size_lt_size_P_first s0 s1 s2))
          | inl hxs =>
            have he := List.mem_singleton.mp hxs
            cases he
            exact And.intro h1 (T.size_lt_size_P_second s0 s1 s2)
    | isFalse hu =>
      rw [T.G_P_of_not_le u s0 s1 s2 hu] at hx
      have hp := ih2 x hx
      exact And.intro hp.1 (Nat.lt_trans hp.2 (T.size_lt_size_P_third s0 s1 s2))

namespace T

open OCF

noncomputable def denote : T → Ordinal.{0}
  | Z => 0
  | P s0 s1 s2 => Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + denote s2

theorem denote_P (s0 s1 s2 : T) :
    denote (P s0 s1 s2) = Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + denote s2 := rfl

theorem denote_head_P (s0 s1 s2 : T) :
    denote (head (P s0 s1 s2)) = Collapse.psi Collapse.hierarchy (denote s0) (denote s1) := by
  change Collapse.psi Collapse.hierarchy (denote s0) (denote s1) + 0 = _
  exact Ordinal.add_zero _

theorem denote_P_pos (s0 s1 s2 : T) : 0 < denote (P s0 s1 s2) :=
  Ordinal.lt_of_lt_of_le (Ordinal.lt_of_lt_of_le (Collapse.hierarchy_pos (denote s0))
    (Collapse.psi_lower_bound Collapse.hierarchy (denote s0) (denote s1)))
    (Ordinal.le_add _ (denote s2))

/-- Order preservation, closure membership, and a principal upper bound are proved together. -/
theorem interpretation_properties (s : T) (hs : isNF s) :
    (∀ t, s < t → denote s < denote t) ∧
    (∀ u b, (∀ x, x ∈ G u s → denote x < b) →
      Collapse.C Collapse.hierarchy (denote u) b (denote s)) ∧
    (∀ b, Ordinal.AddPrincipal b → denote (head s) < b → denote s < b) := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
    cases s with
    | Z =>
      apply And.intro
      · intro t ht
        cases t with
        | Z => exact False.elim (lt_Z_Z_inv ht)
        | P t0 t1 t2 => exact denote_P_pos t0 t1 t2
      · apply And.intro
        · intro u b hb
          exact Collapse.C_base Collapse.hierarchy (denote u) b 0 (Collapse.hierarchy_pos (denote u))
        · intro b hb hZ
          exact hZ
    | P s0 s1 s2 =>
      cases hs with
      | p _ _ _ hs0 hs1 hs2 hG hhead =>
        have ih0 := ih s0 (size_lt_size_P_first s0 s1 s2) hs0
        have ih1 := ih s1 (size_lt_size_P_second s0 s1 s2) hs1
        have ih2 := ih s2 (size_lt_size_P_third s0 s1 s2) hs2
        have headBound : denote (head s2) ≤ denote (head (P s0 s1 s2)) := by
          cases hhead with
          | inl hlt =>
            have hsmall := Nat.lt_of_le_of_lt (head_size_le s2) (size_lt_size_P_third s0 s1 s2)
            exact Or.inl ((ih (head s2) hsmall (head_isNF s2 hs2)).1 (P s0 s1 Z) hlt)
          | inr heq => exact Or.inr (congrArg denote heq)
        have bounded : ∀ b, Ordinal.AddPrincipal b →
            denote (head (P s0 s1 s2)) < b → denote (P s0 s1 s2) < b := by
          intro b hb hfirst
          have htail := ih2.2.2 b hb (Ordinal.lt_of_le_of_lt headBound hfirst)
          rw [denote_head_P] at hfirst
          exact hb _ _ hfirst htail
        have regular : Collapse.C Collapse.hierarchy (denote s0) (denote s1) (denote s1) := by
          apply ih1.2.1 s0 (denote s1)
          intro x hx
          have hp := mem_G_properties s0 s1 x hs1 hx
          have hsmall := Nat.lt_trans hp.2 (size_lt_size_P_second s0 s1 s2)
          exact (ih x hsmall hp.1).1 s1 (hG x hx)
        apply And.intro
        · intro t hst
          cases t with
          | Z => exact False.elim (lt_P_Z_inv s0 s1 s2 hst)
          | P t0 t1 t2 =>
            cases lt_inv s0 s1 s2 t0 t1 t2 hst with
            | inl h0 =>
              have hpsi := Collapse.psi_lt_hierarchy (denote s0) (denote t0) (denote s1) (ih0.1 t0 h0)
              have hsource : denote (P s0 s1 s2) < Collapse.hierarchy (denote t0) := by
                apply bounded _ (Collapse.hierarchy_principal (denote t0))
                rw [denote_head_P]
                exact hpsi
              exact Ordinal.lt_of_lt_of_le hsource
                (Ordinal.le_trans (Collapse.psi_lower_bound Collapse.hierarchy (denote t0) (denote t1))
                  (Ordinal.le_add _ (denote t2)))
            | inr hrest =>
              cases hrest with
              | inl h1 =>
                have heq := h1.1
                have hlt := h1.2
                cases heq
                have hpsi := Collapse.psi_argument_strict (denote s0) (denote s1) (denote t1)
                  (ih1.1 t1 hlt) regular
                have hsource : denote (P s0 s1 s2) <
                    Collapse.psi Collapse.hierarchy (denote s0) (denote t1) := by
                  apply bounded _ (Collapse.psi_hierarchy_principal (denote s0) (denote t1))
                  rw [denote_head_P]
                  exact hpsi
                exact Ordinal.lt_of_lt_of_le hsource (Ordinal.le_add _ (denote t2))
              | inr h2 =>
                have e0 := h2.1
                have e1 := h2.2.1
                have hlt := h2.2.2
                cases e0
                cases e1
                exact Ordinal.add_lt_add_right _ (ih2.1 t2 hlt)
        · apply And.intro
          · intro u b hb
            cases (inferInstance : Decidable (u ≤ s0)) with
            | isTrue hu =>
              have hmember : s1 ∈ G u (P s0 s1 s2) := by
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_left _
                  (List.mem_append_left _ (List.mem_singleton_self s1)))
              have hc0 : Collapse.C Collapse.hierarchy (denote u) b (denote s0) := by
                apply ih0.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
              have hc1 : Collapse.C Collapse.hierarchy (denote u) b (denote s1) := by
                apply ih1.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_left _ (List.mem_append_right _ hx)
              have hc2 : Collapse.C Collapse.hierarchy (denote u) b (denote s2) := by
                apply ih2.2.1 u b
                intro x hx
                apply hb x
                rw [G_P_of_le u s0 s1 s2 hu]
                exact List.mem_append_right _ hx
              exact Collapse.C_step Collapse.hierarchy (denote u) b
                (denote s0) (denote s1) (denote s2) (hb s1 hmember) hc0 hc1 hc2 regular
            | isFalse hu =>
              have hindex : s0 < u := by
                cases T.lt_total s0 u with
                | inl h => exact h
                | inr hrest =>
                  cases hrest with
                  | inl h => exact False.elim (hu (Or.inl h))
                  | inr h => exact False.elim (hu (Or.inr h.symm))
              apply Collapse.C_base Collapse.hierarchy (denote u) b (denote (P s0 s1 s2))
              apply bounded _ (Collapse.hierarchy_principal (denote u))
              rw [denote_head_P]
              exact Collapse.psi_lt_hierarchy (denote s0) (denote u) (denote s1) (ih0.1 u hindex)
          · exact bounded

theorem denote_strict (s t : T) (hs : isNF s) (hst : s < t) : denote s < denote t :=
  (interpretation_properties s hs).1 t hst

end T

def T.NF := { s : T // T.isNF s }

theorem T.NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 := by
  apply Subrelation.wf (r := fun x y : T.NF => T.denote x.1 < T.denote y.1)
  · intro x y hxy
    exact T.denote_strict x.1 y.1 x.2 hxy
  · exact InvImage.wf (fun x : T.NF => T.denote x.1) OCF.Ordinal.lt_wellFounded

def T.LF (n : Nat) :=
  match n with
  | 0 => Z
  | n' + 1 => P (LF n') Z Z

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P Z Z (T.ofNat n)

theorem T.LF_isNF (n : Nat) : T.isNF (T.LF n) := by
  induction n with
  | zero => exact T.isNF.z
  | succ n ih => exact T.isNF_index (T.LF n) ih

theorem T.ofNat_head_le_one (n : Nat) : T.head (T.ofNat n) ≤ P Z Z Z := by
  cases n with
  | zero => exact T.Z_le (P Z Z Z)
  | succ n => exact Or.inr rfl

theorem T.ofNat_isNF (n : Nat) : T.isNF (T.ofNat n) := by
  induction n with
  | zero => exact T.isNF.z
  | succ n ih =>
    apply T.isNF.p Z Z (T.ofNat n) T.isNF.z T.isNF.z ih
    · intro x hx
      change x ∈ ([] : List T) at hx
      exact False.elim (List.not_mem_nil hx)
    · exact T.ofNat_head_le_one n

theorem T.mem_G_LF (u : T) (n : Nat) (x : T) (hx : x ∈ T.G u (T.LF n)) : x = Z := by
  induction n with
  | zero =>
    change x ∈ ([] : List T) at hx
    exact False.elim (List.not_mem_nil hx)
  | succ n ih =>
    change x ∈ T.G u (P (T.LF n) Z Z) at hx
    cases (inferInstance : Decidable (u ≤ T.LF n)) with
    | isTrue hu =>
      rw [T.G_P_of_le u (T.LF n) Z Z hu] at hx
      cases List.mem_append.mp hx with
      | inr hx2 => exact False.elim (List.not_mem_nil hx2)
      | inl hx01 =>
        cases List.mem_append.mp hx01 with
        | inr hx1 => exact False.elim (List.not_mem_nil hx1)
        | inl hx0 =>
          cases List.mem_append.mp hx0 with
          | inl hxZ => exact List.mem_singleton.mp hxZ
          | inr hxn => exact ih hxn
    | isFalse hu =>
      rw [T.G_P_of_not_le u (T.LF n) Z Z hu] at hx
      exact False.elim (List.not_mem_nil hx)

theorem T.base_isNF (n : Nat) : T.isNF (P Z (T.LF n) Z) := by
  apply T.isNF.p Z (T.LF n) Z T.isNF.z (T.LF_isNF n) T.isNF.z
  · intro x hx
    cases n with
    | zero =>
      change x ∈ ([] : List T) at hx
      exact False.elim (List.not_mem_nil hx)
    | succ n =>
      have hxZ := T.mem_G_LF Z (n + 1) x hx
      rw [hxZ]
      exact T.lt.Z_lt_P (T.LF n) Z Z
  · exact T.Z_le (P Z (T.LF n) Z)

theorem T.base_lt_omega_one (n : Nat) : P Z (T.LF n) Z < P (P Z Z Z) Z Z :=
  T.lt.p_first Z (T.LF n) Z (P Z Z Z) Z Z (T.lt.Z_lt_P Z Z Z)

theorem T.LF_cofinal (s : T) : ∃ n : Nat, s < T.LF n := by
  induction s with
  | Z => exact Exists.intro 1 (T.lt.Z_lt_P Z Z Z)
  | P s0 s1 s2 ih0 _ _ =>
    cases ih0 with
    | intro n hn =>
      exact Exists.intro (n + 1) (T.lt.p_first s0 s1 s2 (T.LF n) Z Z hn)

theorem T.base_cofinal_below_omega_one (s : T) (hs : s < P (P Z Z Z) Z Z) :
    ∃ n : Nat, s < P Z (T.LF n) Z := by
  cases s with
  | Z => exact Exists.intro 0 (T.lt.Z_lt_P Z (T.LF 0) Z)
  | P s0 s1 s2 =>
    have h0 := T.below_omega_one_index s0 s1 s2 hs
    cases h0
    cases T.LF_cofinal s1 with
    | intro n hn => exact Exists.intro n (T.lt.p_second Z s1 s2 (T.LF n) Z hn)

inductive T.isOT : T → Prop where
| base (n : Nat) : T.isOT (P Z (T.LF n) Z)
| step (s : T) (hs : T.isOT s) (n : Nat) : T.isOT (T.fund s (T.ofNat n))

theorem T.fund_Z (t : T) : T.fund Z t = Z := by
  rw [T.fund]

theorem T.dom_eq_zero (s : T) (h : T.dom s = .Zero) : s = Z := by
  induction s with
  | Z => rfl
  | P s0 s1 s2 ih0 ih1 ih2 =>
    rw [T.dom] at h
    split at h
    · cases h1 : T.dom s1 with
      | Zero =>
        rw [h1] at h
        cases h0 : T.dom s0 with
        | Zero => rw [h0] at h; cases h
        | One => rw [h0] at h; cases h
        | ω => rw [h0] at h; cases h
        | Ω l => rw [h0] at h; cases h
      | One => rw [h1] at h; cases h
      | ω => rw [h1] at h; cases h
      | Ω l =>
        rw [h1] at h
        change (if s0 < l then Dom.ω else Dom.Ω l) = Dom.Zero at h
        split at h
        · cases h
        · cases h
    · rename_i hne
      exact False.elim (hne (ih2 h))

theorem T.dom_omega_index_one (s l : T) (h : T.dom s = .Ω l) : T.dom l = .One := by
  induction s generalizing l with
  | Z => cases h
  | P s0 s1 s2 ih0 ih1 ih2 =>
    rw [T.dom] at h
    split at h
    · cases h1 : T.dom s1 with
      | Zero =>
        rw [h1] at h
        cases h0 : T.dom s0 with
        | Zero => rw [h0] at h; cases h
        | One => rw [h0] at h; cases h; exact h0
        | ω => rw [h0] at h; cases h
        | Ω m => rw [h0] at h; cases h; exact ih0 _ h0
      | One => rw [h1] at h; cases h
      | ω => rw [h1] at h; cases h
      | Ω m =>
        rw [h1] at h
        change (if s0 < m then Dom.ω else Dom.Ω m) = Dom.Ω l at h
        split at h
        · cases h
        · cases h; exact ih1 _ h1
    · exact ih2 l h

theorem T.add_P (a b c t : T) : P a b c + t = P a b (c + t) := by
  cases t with
  | Z =>
    cases c with
    | Z => rfl
    | P c0 c1 c2 => rfl
  | P t0 t1 t2 => rfl

theorem T.mul_principal_cases (a b t : T) :
    T.mul (P a b Z) t = Z ∨ ∃ r, T.mul (P a b Z) t = P a b r := by
  induction t with
  | Z => exact Or.inl rfl
  | P t0 t1 t2 _ _ ih =>
    rw [T.mul]
    cases ih with
    | inl heq => rw [heq]; exact Or.inr ⟨Z, rfl⟩
    | inr hr =>
      cases hr with
      | intro r hr =>
        rw [hr, T.add_P]
        exact Or.inr ⟨r + P a b Z, rfl⟩

theorem T.mul_lt_P (a b c t : T) (h : b < c) : T.mul (P a b Z) t < P a c Z := by
  cases T.mul_principal_cases a b t with
  | inl heq => rw [heq]; exact T.lt.Z_lt_P a c Z
  | inr hr =>
    cases hr with
    | intro r hr => rw [hr]; exact T.lt.p_second a b r c Z h

theorem T.iter_lt (F : T → T) (t k : T) (hZ : Z < k) (hF : ∀ x, F x < k) :
    T.iter F t < k := by
  cases t with
  | Z => exact hZ
  | P t0 t1 t2 => exact hF (T.iter F t2)

/-- Every recursive call decreases the term when the argument belongs to its domain. -/
theorem T.fund_lt_of_domain (s t : T) (hne : s ≠ Z)
    (ht : ∀ l, T.dom s = .Ω l → t < P l Z Z) : T.fund s t < s := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
    cases s with
    | Z => exact False.elim (hne rfl)
    | P s0 s1 s2 =>
      by_cases h2 : s2 = Z
      · cases h2
        rw [T.fund, ite_eq_left rfl]
        cases h1 : T.dom s1 with
        | Zero =>
          have e1 := T.dom_eq_zero s1 h1
          cases e1
          cases h0 : T.dom s0 with
          | Zero => exact T.lt.Z_lt_P s0 Z Z
          | One =>
            apply ht s0
            rw [T.dom, ite_eq_left rfl]
            change (match T.dom s0 with
              | .Zero => Dom.One | .One => Dom.Ω s0 | .ω => Dom.ω | .Ω l => Dom.Ω l) = _
            rw [h0]
          | ω =>
            apply T.lt.p_first
            apply ih s0 (T.size_lt_size_P_first s0 Z Z) t
            · intro heq; cases heq; cases h0
            · intro l hl; rw [h0] at hl; cases hl
          | Ω l =>
            apply T.lt.p_first
            apply ih s0 (T.size_lt_size_P_first s0 Z Z) t
            · intro heq; cases heq; cases h0
            · intro m hm
              apply ht m
              rw [T.dom, ite_eq_left rfl]
              change (match T.dom s0 with
                | .Zero => Dom.One | .One => Dom.Ω s0 | .ω => Dom.ω | .Ω l => Dom.Ω l) = _
              rw [hm]
        | One =>
          apply T.mul_lt_P
          apply ih s1 (T.size_lt_size_P_second s0 s1 Z) Z
          · intro heq; cases heq; cases h1
          · intro l hl; exact T.lt.Z_lt_P l Z Z
        | ω =>
          apply T.lt.p_second
          apply ih s1 (T.size_lt_size_P_second s0 s1 Z) t
          · intro heq; cases heq; cases h1
          · intro l hl; rw [h1] at hl; cases hl
        | Ω l =>
          change (if s0 < l then P s0 (T.fund s1 (T.iter (fun x => P (T.fund l Z) (T.fund s1 x) Z) t)) Z else P s0 (T.fund s1 t) Z) < P s0 s1 Z
          by_cases h0l : s0 < l
          · rw [ite_eq_left h0l]
            apply T.lt.p_second
            apply ih s1 (T.size_lt_size_P_second s0 s1 Z)
            · intro heq; cases heq; cases h1
            · intro m hm
              rw [h1] at hm
              cases hm
              apply T.iter_lt
              · exact T.lt.Z_lt_P l Z Z
              · intro x
                apply T.lt.p_first
                apply ih l (Nat.lt_trans (T.dom_omega_size s1 l h1)
                  (T.size_lt_size_P_second s0 s1 Z)) Z
                · intro heq
                  have hl := T.dom_omega_index_one s1 l h1
                  rw [heq] at hl
                  cases hl
                · intro k hk; exact T.lt.Z_lt_P k Z Z
          · rw [ite_eq_right h0l]
            apply T.lt.p_second
            apply ih s1 (T.size_lt_size_P_second s0 s1 Z) t
            · intro heq; cases heq; cases h1
            · intro m hm
              rw [h1] at hm
              cases hm
              apply ht l
              rw [T.dom, ite_eq_left rfl, h1]
              change (if s0 < l then Dom.ω else Dom.Ω l) = Dom.Ω l
              rw [ite_eq_right h0l]
      · rw [T.fund, ite_eq_right h2]
        apply T.lt.p_third
        apply ih s2 (T.size_lt_size_P_third s0 s1 s2) t h2
        intro l hl
        apply ht l
        rw [T.dom, ite_eq_right h2]
        exact hl

theorem T.first_le_of_head_le (a b c d e : T) (h : T.head (P a b c) ≤ P d e Z) :
    a ≤ d := by
  cases h with
  | inr heq => cases heq; exact Or.inr rfl
  | inl hlt =>
    cases lt_inv a b Z d e Z hlt with
    | inl h0 => exact Or.inl h0
    | inr hr =>
      cases hr with
      | inl h1 => exact Or.inr h1.1
      | inr h2 => exact Or.inr h2.1

theorem T.le_of_not_lt (a b : T) (h : ¬ a < b) : b ≤ a := by
  cases T.lt_total a b with
  | inl hab => exact False.elim (h hab)
  | inr hr =>
    cases hr with
    | inl hba => exact Or.inl hba
    | inr heq => exact Or.inr heq.symm

theorem T.dom_omega_index_bound (s : T) (hs : T.isNF s) :
    ∀ l, T.dom s = .Ω l → ∃ a b c, s = P a b c ∧ l ≤ a := by
  induction hs with
  | z => intro l hl; cases hl
  | p s0 s1 s2 hs0 hs1 hs2 hG hhead ih0 ih1 ih2 =>
    intro l hl
    refine ⟨s0, s1, s2, rfl, ?_⟩
    rw [T.dom] at hl
    split at hl
    · cases h1 : T.dom s1 with
      | Zero =>
        rw [h1] at hl
        cases h0 : T.dom s0 with
        | Zero => rw [h0] at hl; cases hl
        | One => rw [h0] at hl; cases hl; exact Or.inr rfl
        | ω => rw [h0] at hl; cases hl
        | Ω m =>
          rw [h0] at hl
          cases hl
          cases ih0 l h0 with
          | intro a ha =>
            cases ha with
            | intro b hb =>
              cases hb with
              | intro c hc =>
                rw [hc.1]
                exact Or.inl (lt_of_le_of_lt_thm T l a (P a b c) hc.2 (T.first_lt a b c))
      | One => rw [h1] at hl; cases hl
      | ω => rw [h1] at hl; cases hl
      | Ω m =>
        rw [h1] at hl
        change (if s0 < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hl
        split at hl
        · cases hl
        · rename_i hn
          cases hl
          exact T.le_of_not_lt s0 l hn
    · cases ih2 l hl with
      | intro a ha =>
        cases ha with
        | intro b hb =>
          cases hb with
          | intro c hc =>
            rw [hc.1] at hhead
            exact partial_order.trans l a s0 hc.2 (T.first_le_of_head_le a b c s0 s1 hhead)

theorem T.dom_ne_omega_below_omega_one (s : T) (hs : T.isNF s)
    (hb : s < P (P Z Z Z) Z Z) (l : T) : T.dom s ≠ .Ω l := by
  intro hl
  cases T.dom_omega_index_bound s hs l hl with
  | intro a ha =>
    cases ha with
    | intro b hb' =>
      cases hb' with
      | intro c hc =>
        have hfirst := hc.2
        rw [hc.1] at hb
        have heq := T.below_omega_one_index a b c hb
        rw [heq] at hfirst
        have hlZ : l = Z := by
          cases hfirst with
          | inl hlt => exact False.elim (lt_Z_inv l hlt)
          | inr he => exact he
        have hOne := T.dom_omega_index_one s l hl
        rw [hlZ] at hOne
        cases hOne

theorem T.fund_lt_below_omega_one (s : T) (hs : T.isNF s)
    (hb : s < P (P Z Z Z) Z Z) (hne : s ≠ Z) (t : T) : T.fund s t < s := by
  apply T.fund_lt_of_domain s t hne
  intro l hl
  exact False.elim (T.dom_ne_omega_below_omega_one s hs hb l hl)


theorem T.head_mono (s t : T) (h : s ≤ t) : T.head s ≤ T.head t := by
  cases h with
  | inr heq => cases heq; exact Or.inr rfl
  | inl hlt =>
    cases s with
    | Z => exact T.Z_le (T.head t)
    | P s0 s1 s2 =>
      cases t with
      | Z => exact False.elim (lt_P_Z_inv s0 s1 s2 hlt)
      | P t0 t1 t2 =>
        cases hlt with
        | p_first _ _ _ _ _ _ h0 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
        | p_second _ _ _ _ _ h1 => exact Or.inl (T.lt.p_second _ _ _ _ _ h1)
        | p_third _ _ _ _ h2 => exact Or.inr rfl

theorem T.isNF_replace_tail (a b c t : T) (hs : T.isNF (P a b c))
    (ht : T.isNF t) (hle : t ≤ c) : T.isNF (P a b t) := by
  cases hs with
  | p _ _ _ ha hb hc hG hhead =>
    exact T.isNF.p a b t ha hb ht hG
      (partial_order.trans (T.head t) (T.head c) (P a b Z) (T.head_mono t c hle) hhead)

theorem T.dom_one_cases (s : T) (h : T.dom s = .One) :
    s = P Z Z Z ∨ ∃ a b c, s = P a b c ∧ c ≠ Z ∧ T.dom c = .One := by
  cases s with
  | Z => cases h
  | P a b c =>
    by_cases hc : c = Z
    · cases hc
      rw [T.dom, ite_eq_left rfl] at h
      cases hb : T.dom b with
      | Zero =>
        rw [hb] at h
        cases ha : T.dom a with
        | Zero =>
          have ea := T.dom_eq_zero a ha
          have eb := T.dom_eq_zero b hb
          cases ea
          cases eb
          exact Or.inl rfl
        | One => rw [ha] at h; cases h
        | ω => rw [ha] at h; cases h
        | Ω l => rw [ha] at h; cases h
      | One => rw [hb] at h; cases h
      | ω => rw [hb] at h; cases h
      | Ω l =>
        rw [hb] at h
        change (if a < l then Dom.ω else Dom.Ω l) = Dom.One at h
        split at h
        · cases h
        · cases h
    · refine Or.inr ⟨a, b, c, rfl, hc, ?_⟩
      rw [T.dom, ite_eq_right hc] at h
      exact h

theorem T.fund_one_properties (s : T) (h : T.dom s = .One) :
    (∀ t, T.fund s t = T.fund s Z) ∧
    s = T.fund s Z + P Z Z Z ∧
    (∀ r, r < s → r ≤ T.fund s Z) ∧
    (∀ u x, x ∈ T.G u (T.fund s Z) → x ∈ T.G u s) := by
  induction s with
  | Z => cases h
  | P a b c ih0 ih1 ih2 =>
    cases T.dom_one_cases (P a b c) h with
    | inl heq =>
      cases heq
      have hfund : ∀ t, T.fund (P Z Z Z) t = Z := by
        intro t
        rw [T.fund, ite_eq_left rfl]
        rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t; rw [hfund t, hfund Z]
      · rw [hfund Z]; rfl
      · intro r hr
        rw [hfund Z, T.lt_one_inv r hr]
        exact Or.inr rfl
      · intro u x hx
        rw [hfund Z] at hx
        exact False.elim (List.not_mem_nil hx)
    | inr hrest =>
      cases hrest with
      | intro a' ha' =>
        cases ha' with
        | intro b' hb' =>
          cases hb' with
          | intro c' hc' =>
            cases hc'.1
            have hc := hc'.2.1
            have hd := hc'.2.2
            have ih := ih2 hd
            have hfund : ∀ t, T.fund (P a b c) t = P a b (T.fund c t) := by
              intro t
              rw [T.fund, ite_eq_right hc]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro t; rw [hfund t, hfund Z, ih.1 t]
            · rw [hfund Z, T.add_P]
              exact congrArg (P a b) ih.2.1
            · intro r hr
              rw [hfund Z]
              cases r with
              | Z => exact T.Z_le _
              | P r0 r1 r2 =>
                cases hr with
                | p_first _ _ _ _ _ _ h0 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
                | p_second _ _ _ _ _ h1 => exact Or.inl (T.lt.p_second _ _ _ _ _ h1)
                | p_third _ _ _ _ h2 =>
                  cases ih.2.2.1 r2 h2 with
                  | inl hlt => exact Or.inl (T.lt.p_third _ _ _ _ hlt)
                  | inr heq => cases heq; exact Or.inr rfl
            · intro u x hx
              rw [hfund Z] at hx
              by_cases hua : u ≤ a
              · rw [T.G_P_of_le u a b (T.fund c Z) hua] at hx
                rw [T.G_P_of_le u a b c hua]
                cases List.mem_append.mp hx with
                | inl hx => exact List.mem_append_left _ hx
                | inr hx => exact List.mem_append_right _ (ih.2.2.2 u x hx)
              · rw [T.G_P_of_not_le u a b (T.fund c Z) hua] at hx
                rw [T.G_P_of_not_le u a b c hua]
                exact ih.2.2.2 u x hx

theorem T.fund_one_isNF (s : T) (hs : T.isNF s) (hd : T.dom s = .One) (t : T) :
    T.isNF (T.fund s t) := by
  induction hs with
  | z => cases hd
  | p a b c ha hb hc hG hhead ih0 ih1 ih2 =>
    cases T.dom_one_cases (P a b c) hd with
    | inl heq =>
      rw [heq, T.fund, ite_eq_left rfl]
      exact T.isNF.z
    | inr hex =>
      cases hex with
      | intro a' ha' =>
        cases ha' with
        | intro b' hb' =>
          cases hb' with
          | intro c' hc' =>
            cases hc'.1
            rw [T.fund, ite_eq_right hc'.2.1]
            apply T.isNF_replace_tail a b c (T.fund c t)
              (T.isNF.p a b c ha hb hc hG hhead) (ih2 hc'.2.2)
            apply Or.inl
            apply T.fund_lt_of_domain c t hc'.2.1
            intro l hl
            rw [hc'.2.2] at hl
            cases hl

theorem T.fund_one_regular (u s : T) (hs : T.isNF s) (hd : T.dom s = .One)
    (hG : ∀ x, x ∈ T.G u s → x < s) :
    ∀ x, x ∈ T.G u (T.fund s Z) → x < T.fund s Z := by
  intro x hx
  have hp := T.fund_one_properties s hd
  have hxs := hG x (hp.2.2.2 u x hx)
  have hle := hp.2.2.1 x hxs
  cases hle with
  | inl hlt => exact hlt
  | inr heq =>
    have hsize := (T.mem_G_properties u (T.fund s Z) x (T.fund_one_isNF s hs hd Z) hx).2
    rw [heq] at hsize
    exact False.elim (Nat.lt_irrefl _ hsize)

theorem T.mul_principal_add (a b t : T) :
    T.mul (P a b Z) t + P a b Z = P a b (T.mul (P a b Z) t) := by
  induction t with
  | Z => rfl
  | P t0 t1 t2 _ _ ih =>
    change (T.mul (P a b Z) t2 + P a b Z) + P a b Z =
      P a b (T.mul (P a b Z) t2 + P a b Z)
    rw [ih, T.add_P, ih]

theorem T.mul_principal_head_le (a b t : T) :
    T.head (T.mul (P a b Z) t) ≤ P a b Z := by
  cases T.mul_principal_cases a b t with
  | inl heq => rw [heq]; exact T.Z_le _
  | inr hex =>
    cases hex with
    | intro r hr => rw [hr]; exact Or.inr rfl

theorem T.mul_principal_isNF (a b t : T) (h : T.isNF (P a b Z)) :
    T.isNF (T.mul (P a b Z) t) := by
  induction t with
  | Z => exact T.isNF.z
  | P t0 t1 t2 _ _ ih =>
    rw [T.mul, T.mul_principal_add]
    cases h with
    | p _ _ _ ha hb hZ hG hhead =>
      exact T.isNF.p a b (T.mul (P a b Z) t2) ha hb ih hG
        (T.mul_principal_head_le a b t2)

theorem T.fund_principal_successor_isNF (a b t : T) (hs : T.isNF (P a b Z))
    (hb : T.dom b = .One) : T.isNF (T.fund (P a b Z) t) := by
  cases hs with
  | p _ _ _ ha hbNF hZ hG hhead =>
    rw [T.fund, ite_eq_left rfl, hb]
    apply T.mul_principal_isNF
    exact T.isNF.p a (T.fund b Z) Z ha (T.fund_one_isNF b hbNF hb Z) T.isNF.z
      (T.fund_one_regular a b hbNF hb hG) (T.Z_le _)

theorem T.lt_principal_of_head_lt (r a b : T) (hr : T.head r < P a b Z) :
    r < P a b Z := by
  cases r with
  | Z => exact T.lt.Z_lt_P a b Z
  | P r0 r1 r2 =>
    cases hr with
    | p_first _ _ _ _ _ _ h0 => exact T.lt.p_first _ _ _ _ _ _ h0
    | p_second _ _ _ _ _ h1 => exact T.lt.p_second _ _ _ _ _ h1
    | p_third _ _ _ _ h2 => exact False.elim (lt_Z_Z_inv h2)

theorem T.mul_principal_ofNat_succ (a b : T) (n : Nat) :
    T.mul (P a b Z) (T.ofNat (n + 1)) = P a b (T.mul (P a b Z) (T.ofNat n)) := by
  change T.mul (P a b Z) (T.ofNat n) + P a b Z = _
  exact T.mul_principal_add a b (T.ofNat n)

theorem T.mul_principal_cofinal (a b r : T) (hr : T.isNF r)
    (hhead : T.head r ≤ P a b Z) :
    ∃ n : Nat, r < T.mul (P a b Z) (T.ofNat n) := by
  induction hr with
  | z => exact ⟨1, T.lt.Z_lt_P a b Z⟩
  | p r0 r1 r2 hr0 hr1 hr2 hG htail ih0 ih1 ih2 =>
    cases hhead with
    | inl hh => exact ⟨1, T.lt_principal_of_head_lt (P r0 r1 r2) a b hh⟩
    | inr heq =>
      change P r0 r1 Z = P a b Z at heq
      cases heq
      cases ih2 htail with
      | intro n hn =>
        refine ⟨n + 1, ?_⟩
        rw [T.mul_principal_ofNat_succ]
        exact T.lt.p_third _ _ _ _ hn

theorem T.fund_principal_successor_cofinal (a b r : T) (hb : T.dom b = .One)
    (hr : T.isNF r) (hrs : r < P a b Z) :
    ∃ n : Nat, r ≤ T.fund (P a b Z) (T.ofNat n) := by
  have hhead : T.head r ≤ P a (T.fund b Z) Z := by
    cases r with
    | Z => exact T.Z_le _
    | P r0 r1 r2 =>
      cases hrs with
      | p_first _ _ _ _ _ _ h0 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
      | p_second _ _ _ _ _ h1 =>
        cases (T.fund_one_properties b hb).2.2.1 r1 h1 with
        | inl hlt => exact Or.inl (T.lt.p_second _ _ _ _ _ hlt)
        | inr heq => cases heq; exact Or.inr rfl
      | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
  cases T.mul_principal_cofinal a (T.fund b Z) r hr hhead with
  | intro n hn =>
    refine ⟨n, Or.inl ?_⟩
    rw [T.fund, ite_eq_left rfl, hb]
    exact hn


def T.GBound (u s b : T) : Prop := ∀ x, x ∈ T.G u s → x < b

theorem T.GBound_zero (u b : T) : T.GBound u Z b := by
  intro x hx
  exact False.elim (List.not_mem_nil hx)

theorem T.GBound_P (u a b c k : T) : T.GBound u (P a b c) k ↔
    (u ≤ a → b < k ∧ T.GBound u a k ∧ T.GBound u b k) ∧ T.GBound u c k := by
  apply Iff.intro
  · intro h
    apply And.intro
    · intro hu
      have hm : ∀ x, x ∈ [b] ++ T.G u a ++ T.G u b ++ T.G u c → x < k := by
        intro x hx
        apply h x
        rw [T.G_P_of_le u a b c hu]
        exact hx
      refine ⟨?_, ?_, ?_⟩
      · exact hm b (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_singleton_self b))))
      · intro x hx
        exact hm x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
      · intro x hx
        exact hm x (List.mem_append_left _ (List.mem_append_right _ hx))
    · intro x hx
      apply h x
      by_cases hu : u ≤ a
      · rw [T.G_P_of_le u a b c hu]
        exact List.mem_append_right _ hx
      · rw [T.G_P_of_not_le u a b c hu]
        exact hx
  · intro h x hx
    by_cases hu : u ≤ a
    · rw [T.G_P_of_le u a b c hu] at hx
      cases List.mem_append.mp hx with
      | inr hxc => exact h.2 x hxc
      | inl hxab =>
        cases List.mem_append.mp hxab with
        | inr hxb => exact (h.1 hu).2.2 x hxb
        | inl hxa =>
          cases List.mem_append.mp hxa with
          | inr hxa => exact (h.1 hu).2.1 x hxa
          | inl hxb => rw [List.mem_singleton.mp hxb]; exact (h.1 hu).1
    · rw [T.G_P_of_not_le u a b c hu] at hx
      exact h.2 x hx

theorem T.dom_omega_index_lt (s l : T) (hs : T.isNF s) (hd : T.dom s = .Ω l) : l < s := by
  cases T.dom_omega_index_bound s hs l hd with
  | intro a ha =>
    cases ha with
    | intro b hb =>
      cases hb with
      | intro c hc =>
        rw [hc.1]
        exact lt_of_le_of_lt_thm T l a (P a b c) hc.2 (T.first_lt a b c)

theorem T.dom_omega_index_isNF (s l : T) (hs : T.isNF s) (hd : T.dom s = .Ω l) :
    T.isNF l := by
  induction hs generalizing l with
  | z => cases hd
  | p a b c ha hb hc hG hhead ih0 ih1 ih2 =>
    rw [T.dom] at hd
    split at hd
    · cases h1 : T.dom b with
      | Zero =>
        rw [h1] at hd
        cases h0 : T.dom a with
        | Zero => rw [h0] at hd; cases hd
        | One => rw [h0] at hd; cases hd; exact ha
        | ω => rw [h0] at hd; cases hd
        | Ω m => rw [h0] at hd; cases hd; exact ih0 l h0
      | One => rw [h1] at hd; cases hd
      | ω => rw [h1] at hd; cases hd
      | Ω m =>
        rw [h1] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        split at hd
        · cases hd
        · cases hd; exact ih1 l h1
    · exact ih2 l hd

theorem T.GBound_dom_index (s l u k : T) (hs : T.isNF s) (hd : T.dom s = .Ω l)
    (hu : u ≤ l) (hG : T.GBound u s k) : T.GBound u l k := by
  induction hs generalizing l with
  | z => cases hd
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hparts := (T.GBound_P u a b c k).mp hG
    rw [T.dom] at hd
    split at hd
    · cases h1 : T.dom b with
      | Zero =>
        rw [h1] at hd
        cases h0 : T.dom a with
        | Zero => rw [h0] at hd; cases hd
        | One => rw [h0] at hd; cases hd; exact (hparts.1 hu).2.1
        | ω => rw [h0] at hd; cases hd
        | Ω m =>
          rw [h0] at hd
          cases hd
          have hua : u ≤ a := Or.inl (lt_of_le_of_lt_thm T u l a hu
            (T.dom_omega_index_lt a l ha h0))
          exact ih0 l h0 hu (hparts.1 hua).2.1
      | One => rw [h1] at hd; cases hd
      | ω => rw [h1] at hd; cases hd
      | Ω m =>
        rw [h1] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        split at hd
        · cases hd
        · rename_i hn
          cases hd
          have hua := partial_order.trans u l a hu (T.le_of_not_lt a l hn)
          exact ih1 l h1 hu (hparts.1 hua).2.2
    · exact ih2 l hd hu hparts.2

theorem T.GBound_mul_principal (u a b k t : T) (hG : T.GBound u (P a b Z) k) :
    T.GBound u (T.mul (P a b Z) t) k := by
  induction t with
  | Z => exact T.GBound_zero u k
  | P t0 t1 t2 _ _ ih =>
    rw [T.mul, T.mul_principal_add]
    exact (T.GBound_P u a b (T.mul (P a b Z) t2) k).mpr
      ⟨((T.GBound_P u a b Z k).mp hG).1, ih⟩

theorem T.GBound_fund_one (u s k : T) (hd : T.dom s = .One) (hG : T.GBound u s k) :
    T.GBound u (T.fund s Z) k := by
  intro x hx
  exact hG x ((T.fund_one_properties s hd).2.2.2 u x hx)

/-- Applying a basic-sequence operation introduces no support above an existing bound. -/
theorem T.GBound_fund (s : T) (hs : T.isNF s) (u k t : T)
    (hd : ∀ l, T.dom s = .Ω l → t < P l Z Z)
    (hG : T.GBound u s k) (ht : T.GBound u t k) : T.GBound u (T.fund s t) k := by
  induction hs generalizing t with
  | z => rw [T.fund_Z]; exact T.GBound_zero u k
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hparts := (T.GBound_P u a b c k).mp hG
    by_cases hcZ : c = Z
    · cases hcZ
      rw [T.fund, ite_eq_left rfl]
      cases hbdom : T.dom b with
      | Zero =>
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        cases hadom : T.dom a with
        | Zero => exact T.GBound_zero u k
        | One => exact ht
        | ω =>
          apply (T.GBound_P u (T.fund a t) Z Z k).mpr
          refine ⟨?_, T.GBound_zero u k⟩
          intro hu
          have hane : a ≠ Z := by intro heq; cases heq; cases hadom
          have had : ∀ l, T.dom a = .Ω l → t < P l Z Z := by
            intro l hl; rw [hadom] at hl; cases hl
          have hua : u ≤ a := Or.inl (lt_of_le_of_lt_thm T u (T.fund a t) a hu
            (T.fund_lt_of_domain a t hane had))
          have hp := hparts.1 hua
          exact ⟨hp.1, ih0 t had hp.2.1 ht, T.GBound_zero u k⟩
        | Ω l =>
          apply (T.GBound_P u (T.fund a t) Z Z k).mpr
          refine ⟨?_, T.GBound_zero u k⟩
          intro hu
          have hane : a ≠ Z := by intro heq; cases heq; cases hadom
          have had : ∀ m, T.dom a = .Ω m → t < P m Z Z := by
            intro m hm
            apply hd m
            rw [T.dom, ite_eq_left rfl]
            change (match T.dom a with
              | .Zero => Dom.One | .One => Dom.Ω a | .ω => Dom.ω | .Ω n => Dom.Ω n) = _
            rw [hm]
          have hua : u ≤ a := Or.inl (lt_of_le_of_lt_thm T u (T.fund a t) a hu
            (T.fund_lt_of_domain a t hane had))
          have hp := hparts.1 hua
          exact ⟨hp.1, ih0 t had hp.2.1 ht, T.GBound_zero u k⟩
      | One =>
        apply T.GBound_mul_principal
        apply (T.GBound_P u a (T.fund b Z) Z k).mpr
        refine ⟨?_, T.GBound_zero u k⟩
        intro hu
        have hp := hparts.1 hu
        have hbne : b ≠ Z := by intro heq; cases heq; cases hbdom
        have hbdesc := T.fund_lt_of_domain b Z hbne (fun l _ => T.lt.Z_lt_P l Z Z)
        exact ⟨T.lt_trans _ _ _ hbdesc hp.1, hp.2.1, T.GBound_fund_one u b k hbdom hp.2.2⟩
      | ω =>
        apply (T.GBound_P u a (T.fund b t) Z k).mpr
        refine ⟨?_, T.GBound_zero u k⟩
        intro hu
        have hp := hparts.1 hu
        have hbne : b ≠ Z := by intro heq; cases heq; cases hbdom
        have hbd : ∀ l, T.dom b = .Ω l → t < P l Z Z := by
          intro l hl; rw [hbdom] at hl; cases hl
        have hbdesc := T.fund_lt_of_domain b t hbne hbd
        exact ⟨T.lt_trans _ _ _ hbdesc hp.1, hp.2.1, ih1 t hbd hp.2.2 ht⟩
      | Ω l =>
        change T.GBound u (if a < l then
          P a (T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) t)) Z
          else P a (T.fund b t) Z) k
        have hbne : b ≠ Z := by intro heq; cases heq; cases hbdom
        by_cases hal : a < l
        · rw [ite_eq_left hal]
          apply (T.GBound_P u a _ Z k).mpr
          refine ⟨?_, T.GBound_zero u k⟩
          intro hu
          have hp := hparts.1 hu
          have hlone := T.dom_omega_index_one b l hbdom
          have hlne : l ≠ Z := by intro heq; rw [heq] at hlone; cases hlone
          have hldesc := T.fund_lt_of_domain l Z hlne (fun m _ => T.lt.Z_lt_P m Z Z)
          have hlG := T.GBound_dom_index b l u k hb hbdom
            (Or.inl (lt_of_le_of_lt_thm T u a l hu hal)) hp.2.2
          have hlpG := T.GBound_fund_one u l k hlone hlG
          let F := fun x => P (T.fund l Z) (T.fund b x) Z
          have hiter : ∀ z, T.iter F z < P l Z Z ∧ T.GBound u (T.iter F z) k := by
            intro z
            induction z with
            | Z => exact ⟨T.lt.Z_lt_P l Z Z, T.GBound_zero u k⟩
            | P z0 z1 z2 _ _ ih =>
              change F (T.iter F z2) < P l Z Z ∧ T.GBound u (F (T.iter F z2)) k
              apply And.intro (T.lt.p_first _ _ _ _ _ _ hldesc)
              apply (T.GBound_P u (T.fund l Z) (T.fund b (T.iter F z2)) Z k).mpr
              refine ⟨?_, T.GBound_zero u k⟩
              intro hu'
              have hbd : ∀ m, T.dom b = .Ω m → T.iter F z2 < P m Z Z := by
                intro m hm; rw [hbdom] at hm; cases hm; exact ih.1
              exact ⟨T.lt_trans _ _ _ (T.fund_lt_of_domain b _ hbne hbd) hp.1,
                hlpG, ih1 _ hbd hp.2.2 ih.2⟩
          have htiter := hiter t
          have hbd : ∀ m, T.dom b = .Ω m → T.iter F t < P m Z Z := by
            intro m hm; rw [hbdom] at hm; cases hm; exact htiter.1
          exact ⟨T.lt_trans _ _ _ (T.fund_lt_of_domain b _ hbne hbd) hp.1,
            hp.2.1, ih1 _ hbd hp.2.2 htiter.2⟩
        · rw [ite_eq_right hal]
          apply (T.GBound_P u a (T.fund b t) Z k).mpr
          refine ⟨?_, T.GBound_zero u k⟩
          intro hu
          have hp := hparts.1 hu
          have hbd : ∀ m, T.dom b = .Ω m → t < P m Z Z := by
            intro m hm
            rw [hbdom] at hm
            cases hm
            apply hd l
            rw [T.dom, ite_eq_left rfl, hbdom]
            change (if a < l then Dom.ω else Dom.Ω l) = Dom.Ω l
            rw [ite_eq_right hal]
          exact ⟨T.lt_trans _ _ _ (T.fund_lt_of_domain b t hbne hbd) hp.1,
            hp.2.1, ih1 t hbd hp.2.2 ht⟩
    · rw [T.fund, ite_eq_right hcZ]
      apply (T.GBound_P u a b (T.fund c t) k).mpr
      apply And.intro hparts.1
      apply ih2 t
      · intro l hl
        apply hd l
        rw [T.dom, ite_eq_right hcZ]
        exact hl
      · exact hparts.2
      · exact ht


theorem T.ofNat_lt_index (n : Nat) (l : T) (hl : l ≠ Z) : T.ofNat n < P l Z Z := by
  cases n with
  | zero => exact T.lt.Z_lt_P l Z Z
  | succ n =>
    cases l with
    | Z => exact False.elim (hl rfl)
    | P l0 l1 l2 => exact T.lt.p_first _ _ _ _ _ _ (T.lt.Z_lt_P l0 l1 l2)

theorem T.ofNat_in_domain (s : T) (n : Nat) :
    ∀ l, T.dom s = .Ω l → T.ofNat n < P l Z Z := by
  intro l hl
  apply T.ofNat_lt_index n l
  intro heq
  have hone := T.dom_omega_index_one s l hl
  rw [heq] at hone
  cases hone

theorem T.fund_ofNat_lt (s : T) (n : Nat) (hs : s ≠ Z) : T.fund s (T.ofNat n) < s :=
  T.fund_lt_of_domain s (T.ofNat n) hs (T.ofNat_in_domain s n)

theorem T.mem_G_ofNat (u : T) (n : Nat) (x : T) (hx : x ∈ T.G u (T.ofNat n)) :
    x = Z ∧ u = Z := by
  induction n with
  | zero => exact False.elim (List.not_mem_nil hx)
  | succ n ih =>
    change x ∈ T.G u (P Z Z (T.ofNat n)) at hx
    by_cases hu : u ≤ Z
    · have huZ : u = Z := by
        cases hu with
        | inl hlt => exact False.elim (lt_Z_inv u hlt)
        | inr heq => exact heq
      rw [T.G_P_of_le u Z Z (T.ofNat n) hu] at hx
      cases List.mem_append.mp hx with
      | inr hxn => exact ih hxn
      | inl hx0 =>
        cases List.mem_append.mp hx0 with
        | inr hxZ => exact False.elim (List.not_mem_nil hxZ)
        | inl hx0 =>
          cases List.mem_append.mp hx0 with
          | inr hxZ => exact False.elim (List.not_mem_nil hxZ)
          | inl hxZ => exact ⟨List.mem_singleton.mp hxZ, huZ⟩
    · rw [T.G_P_of_not_le u Z Z (T.ofNat n) hu] at hx
      exact ih hx

theorem T.GBound_fund_ofNat (s : T) (hs : T.isNF s) (u k : T)
    (hG : T.GBound u s k) (n : Nat) : T.GBound u (T.fund s (T.ofNat n)) k := by
  cases s with
  | Z => rw [T.fund_Z]; exact T.GBound_zero u k
  | P a b c =>
    apply T.GBound_fund (P a b c) hs u k (T.ofNat n) (T.ofNat_in_domain _ n) hG
    intro x hx
    have hp := T.mem_G_ofNat u n x hx
    have hg0 : T.GBound Z (P a b c) k := by rw [← hp.2]; exact hG
    have hbk := (((T.GBound_P Z a b c k).mp hg0).1 (T.Z_le a)).1
    rw [hp.1]
    exact lt_of_le_of_lt_thm T Z b k (T.Z_le b) hbk

theorem T.fund_nonzero_tail_isNF (a b c t : T) (hs : T.isNF (P a b c))
    (hc : c ≠ Z) (hct : T.isNF (T.fund c t))
    (hd : ∀ l, T.dom c = .Ω l → t < P l Z Z) :
    T.isNF (T.fund (P a b c) t) := by
  rw [T.fund, ite_eq_right hc]
  exact T.isNF_replace_tail a b c (T.fund c t) hs hct
    (Or.inl (T.fund_lt_of_domain c t hc hd))

theorem T.fund_nonzero_tail_cofinal (a b c r : T) (hc : c ≠ Z)
    (hcofinal : ∀ q, T.isNF q → q < c → ∃ n, q ≤ T.fund c (T.ofNat n))
    (hr : T.isNF r) (hrs : r < P a b c) :
    ∃ n, r ≤ T.fund (P a b c) (T.ofNat n) := by
  cases r with
  | Z =>
    refine ⟨0, ?_⟩
    rw [T.fund, ite_eq_right hc]
    exact T.Z_le _
  | P r0 r1 r2 =>
    cases hrs with
    | p_first _ _ _ _ _ _ h0 =>
      refine ⟨0, ?_⟩
      rw [T.fund, ite_eq_right hc]
      exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
    | p_second _ _ _ _ _ h1 =>
      refine ⟨0, ?_⟩
      rw [T.fund, ite_eq_right hc]
      exact Or.inl (T.lt.p_second _ _ _ _ _ h1)
    | p_third _ _ _ _ h2 =>
      cases hcofinal r2 (T.isNF_components _ _ _ hr).2.2 h2 with
      | intro n hn =>
        refine ⟨n, ?_⟩
        rw [T.fund, ite_eq_right hc]
        cases hn with
        | inl hlt => exact Or.inl (T.lt.p_third _ _ _ _ hlt)
        | inr heq => rw [heq]; exact Or.inr rfl

theorem T.add_one_ne_zero (s : T) : s + P Z Z Z ≠ Z := by
  cases s with
  | Z => intro h; cases h
  | P a b c => rw [T.add_P]; intro h; cases h

theorem T.dom_add_one (s : T) : T.dom (s + P Z Z Z) = .One := by
  induction s with
  | Z => rfl
  | P a b c ih0 ih1 ih2 =>
    rw [T.add_P, T.dom, ite_eq_right (T.add_one_ne_zero c)]
    exact ih2

theorem T.fund_add_one (s t : T) : T.fund (s + P Z Z Z) t = s := by
  induction s with
  | Z =>
    change T.fund (P Z Z Z) t = Z
    rw [T.fund, ite_eq_left rfl]
    rfl
  | P a b c ih0 ih1 ih2 =>
    rw [T.add_P, T.fund, ite_eq_right (T.add_one_ne_zero c), ih2]

theorem T.lt_add_one (s : T) : s < s + P Z Z Z := by
  induction s with
  | Z => exact T.lt.Z_lt_P Z Z Z
  | P a b c ih0 ih1 ih2 =>
    rw [T.add_P]
    exact T.lt.p_third _ _ _ _ ih2

theorem T.add_one_lt_of_dom_ne_one (s r : T) (hs : T.dom s ≠ .One) (hr : r < s) :
    r + P Z Z Z < s := by
  cases T.lt_total (r + P Z Z Z) s with
  | inl hlt => exact hlt
  | inr hrest =>
    cases hrest with
    | inl hlt =>
      have hle := (T.fund_one_properties (r + P Z Z Z) (T.dom_add_one r)).2.2.1 s hlt
      rw [T.fund_add_one] at hle
      exact False.elim (T.lt_irrefl r (lt_of_lt_of_le_thm T r s r hr hle))
    | inr heq =>
      exact False.elim (hs (Eq.trans (congrArg T.dom heq.symm) (T.dom_add_one r)))

theorem T.one_le_P (a b c : T) : P Z Z Z ≤ P a b c := by
  cases T.lt_total (P Z Z Z) (P a b c) with
  | inl hlt => exact Or.inl hlt
  | inr hrest =>
    cases hrest with
    | inl hlt => have heq := T.lt_one_inv _ hlt; cases heq
    | inr heq => exact Or.inr heq

theorem T.add_one_isNF (s : T) (hs : T.isNF s) : T.isNF (s + P Z Z Z) := by
  induction hs with
  | z => exact T.isNF_index Z T.isNF.z
  | p a b c ha hb hc hG hhead ih0 ih1 ih2 =>
    rw [T.add_P]
    apply T.isNF.p a b (c + P Z Z Z) ha hb ih2 hG
    cases c with
    | Z => exact T.one_le_P a b Z
    | P c0 c1 c2 =>
      rw [T.add_P]
      exact hhead

theorem T.add_one_lt_index (s l : T) (hl : l ≠ Z) (h : s < P l Z Z) :
    s + P Z Z Z < P l Z Z := by
  cases s with
  | Z =>
    cases l with
    | Z => exact False.elim (hl rfl)
    | P l0 l1 l2 => exact T.lt.p_first _ _ _ _ _ _ (T.lt.Z_lt_P l0 l1 l2)
  | P a b c =>
    rw [T.add_P]
    cases h with
    | p_first _ _ _ _ _ _ h0 => exact T.lt.p_first _ _ _ _ _ _ h0
    | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
    | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)

theorem T.GBound_add_one (u s k : T) (hk : Z < k) (h : T.GBound u s k) :
    T.GBound u (s + P Z Z Z) k := by
  induction s with
  | Z =>
    apply (T.GBound_P u Z Z Z k).mpr
    exact ⟨fun _ => ⟨hk, T.GBound_zero u k, T.GBound_zero u k⟩, T.GBound_zero u k⟩
  | P a b c ih0 ih1 ih2 =>
    rw [T.add_P]
    have hp := (T.GBound_P u a b c k).mp h
    exact (T.GBound_P u a b (c + P Z Z Z) k).mpr ⟨hp.1, ih2 hp.2⟩

theorem T.GBound_index_mono (s u v k : T) (huv : u ≤ v) (h : T.GBound u s k) :
    T.GBound v s k := by
  induction s with
  | Z => exact T.GBound_zero v k
  | P a b c ih0 ih1 ih2 =>
    have hp := (T.GBound_P u a b c k).mp h
    apply (T.GBound_P v a b c k).mpr
    refine ⟨?_, ih2 hp.2⟩
    intro hv
    have hp' := hp.1 (partial_order.trans u v a huv hv)
    exact ⟨hp'.1, ih0 hp'.2.1, ih1 hp'.2.2⟩

theorem T.GBound_mem (u s x k : T) (h : T.GBound u s k) (hx : x ∈ T.G u s) :
    T.GBound u x k := by
  induction s generalizing x with
  | Z => exact False.elim (List.not_mem_nil hx)
  | P a b c ih0 ih1 ih2 =>
    have hp := (T.GBound_P u a b c k).mp h
    by_cases hu : u ≤ a
    · rw [T.G_P_of_le u a b c hu] at hx
      have hp' := hp.1 hu
      cases List.mem_append.mp hx with
      | inr hxc => exact ih2 x hp.2 hxc
      | inl hx01 =>
        cases List.mem_append.mp hx01 with
        | inr hxb => exact ih1 x hp'.2.2 hxb
        | inl hx0 =>
          cases List.mem_append.mp hx0 with
          | inr hxa => exact ih0 x hp'.2.1 hxa
          | inl hxb => rw [List.mem_singleton.mp hxb]; exact hp'.2.2
    · rw [T.G_P_of_not_le u a b c hu] at hx
      exact ih2 x hp.2 hx

theorem T.GBound_below_index (u s k : T) (hs : T.isNF s) (h : s < P u Z Z) :
    T.GBound u s k := by
  induction hs with
  | z => exact T.GBound_zero u k
  | p a b c ha hb hc hG hhead ih0 ih1 ih2 =>
    have hau : a < u := by
      cases h with
      | p_first _ _ _ _ _ _ h0 => exact h0
      | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
      | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
    have hnot : ¬ u ≤ a := by
      intro hua
      exact T.lt_irrefl a (lt_of_lt_of_le_thm T a u a hau hua)
    have hhead' : P a b Z < P u Z Z := T.lt.p_first _ _ _ _ _ _ hau
    have hclt := T.lt_principal_of_head_lt c u Z
      (lt_of_le_of_lt_thm T (T.head c) (P a b Z) (P u Z Z) hhead hhead')
    intro x hx
    rw [T.G_P_of_not_le u a b c hnot] at hx
    exact ih2 hclt x hx

theorem T.GBound_self (u k : T) (hu : T.isNF u) : T.GBound u u k :=
  T.GBound_below_index u u k hu (T.first_lt u Z Z)

theorem T.index_le_P (l a b c : T) (hla : l ≤ a) : P l Z Z ≤ P a b c := by
  cases hla with
  | inl hlt => exact Or.inl (T.lt.p_first _ _ _ _ _ _ hlt)
  | inr heq =>
    cases heq
    cases b with
    | P b0 b1 b2 => exact Or.inl (T.lt.p_second _ _ _ _ _ (T.lt.Z_lt_P b0 b1 b2))
    | Z =>
      cases c with
      | Z => exact Or.inr rfl
      | P c0 c1 c2 => exact Or.inl (T.lt.p_third _ _ _ _ (T.lt.Z_lt_P c0 c1 c2))

/-- An uncollapsed domain gives a strictly increasing substitution in its argument. -/
theorem T.fund_omega_strict (s l : T) (hd : T.dom s = .Ω l) (t r : T) (htr : t < r) :
    T.fund s t < T.fund s r := by
  induction s generalizing l with
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
        | One => exact htr
        | ω => rw [ha] at hd; cases hd
        | Ω m =>
          rw [ha] at hd
          cases hd
          exact T.lt.p_first _ _ _ _ _ _ (ih0 l ha)
      | One => rw [hb] at hd; cases hd
      | ω => rw [hb] at hd; cases hd
      | Ω m =>
        rw [hb] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        change (if a < m then P a (T.fund b (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) t)) Z
          else P a (T.fund b t) Z) <
          (if a < m then P a (T.fund b (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) r)) Z
          else P a (T.fund b r) Z)
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham] at hd
          rw [ite_eq_right ham, ite_eq_right ham]
          exact T.lt.p_second _ _ _ _ _ (ih1 m hb)
    · rw [T.dom, ite_eq_right hc] at hd
      rw [T.fund, ite_eq_right hc, T.fund, ite_eq_right hc]
      exact T.lt.p_third _ _ _ _ (ih2 l hd)

theorem T.input_le_fund_omega (s l : T) (hs : T.isNF s) (hd : T.dom s = .Ω l)
    (t : T) (ht : t < P l Z Z) : t ≤ T.fund s t := by
  induction hs generalizing l with
  | z => cases hd
  | p a b c ha hb hc hG hhead ih0 ih1 ih2 =>
    have hla : l ≤ a := by
      cases T.dom_omega_index_bound (P a b c) (T.isNF.p a b c ha hb hc hG hhead) l hd with
      | intro a' ha' =>
        cases ha' with
        | intro b' hb' =>
          cases hb' with
          | intro c' hc' => cases hc'.1; exact hc'.2
    by_cases hcZ : c = Z
    · cases hcZ
      rw [T.dom, ite_eq_left rfl] at hd
      rw [T.fund, ite_eq_left rfl]
      cases hbdom : T.dom b with
      | Zero =>
        rw [hbdom] at hd
        cases hadom : T.dom a with
        | Zero => rw [hadom] at hd; cases hd
        | One => exact Or.inr rfl
        | ω => rw [hadom] at hd; cases hd
        | Ω m =>
          rw [hadom] at hd
          cases hd
          exact Or.inl (lt_of_le_of_lt_thm T t (T.fund a t) (P (T.fund a t) Z Z)
            (ih0 l hadom ht) (T.first_lt (T.fund a t) Z Z))
      | One => rw [hbdom] at hd; cases hd
      | ω => rw [hbdom] at hd; cases hd
      | Ω m =>
        rw [hbdom] at hd
        change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
        change t ≤ (if a < m then
          P a (T.fund b (T.iter (fun x => P (T.fund m Z) (T.fund b x) Z) t)) Z
          else P a (T.fund b t) Z)
        by_cases ham : a < m
        · rw [ite_eq_left ham] at hd; cases hd
        · rw [ite_eq_right ham]
          exact Or.inl (lt_of_lt_of_le_thm T t (P l Z Z) _ ht (T.index_le_P l a _ Z hla))
    · rw [T.fund, ite_eq_right hcZ]
      exact Or.inl (lt_of_lt_of_le_thm T t (P l Z Z) _ ht (T.index_le_P l a b _ hla))

/-- Cofinality for an uncollapsed domain, with control of the witness's support. -/
theorem T.fund_omega_cofinal_support (s : T) (hs : T.isNF s) (l u k : T)
    (hd : T.dom s = .Ω l) (hu : T.isNF u) (hul : u ≤ l) (hk : Z < k)
    (r : T) (hr : T.isNF r) (hrs : r < s) (hG : T.GBound u r k) :
    ∃ t, T.isNF t ∧ t < P l Z Z ∧ T.GBound u t k ∧ r < T.fund s t := by
  induction hs generalizing l r with
  | z => exact False.elim (lt_Z_inv r hrs)
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hs := T.isNF.p a b c ha hb hc hreg hhead
    have hlne : l ≠ Z := by
      intro heq
      have hlone := T.dom_omega_index_one (P a b c) l hd
      rw [heq] at hlone
      cases hlone
    cases r with
    | Z =>
      have hOne : P Z Z Z < P l Z Z := T.ofNat_lt_index 1 l hlne
      refine ⟨P Z Z Z, T.isNF_index Z T.isNF.z, hOne, ?_, ?_⟩
      · exact T.GBound_add_one u Z k hk (T.GBound_zero u k)
      · exact lt_of_lt_of_le_thm T Z (P Z Z Z) _ (T.lt.Z_lt_P Z Z Z)
          (T.input_le_fund_omega (P a b c) l hs hd (P Z Z Z) hOne)
    | P r0 r1 r2 =>
      have hcomponents := T.isNF_components r0 r1 r2 hr
      have hparts := (T.GBound_P u r0 r1 r2 k).mp hG
      by_cases hcZ : c = Z
      · cases hcZ
        rw [T.dom, ite_eq_left rfl] at hd
        conv =>
          enter [1, t, 2, 2, 2]
          rw [T.fund, ite_eq_left rfl]
        cases hbdom : T.dom b with
        | Zero =>
          rw [hbdom] at hd
          have hbZ := T.dom_eq_zero b hbdom
          cases hbZ
          cases hadom : T.dom a with
          | Zero => rw [hadom] at hd; cases hd
          | One =>
            rw [hadom] at hd
            cases hd
            exact ⟨P r0 r1 r2 + P Z Z Z, T.add_one_isNF _ hr,
              T.add_one_lt_index _ a hlne hrs, T.GBound_add_one u _ k hk hG,
              T.lt_add_one _⟩
          | ω => rw [hadom] at hd; cases hd
          | Ω m =>
            rw [hadom] at hd
            cases hd
            have hr0a : r0 < a := by
              cases hrs with
              | p_first _ _ _ _ _ _ h0 => exact h0
              | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
              | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
            by_cases hur : u ≤ r0
            · cases ih0 l hadom hul r0 hcomponents.1 hr0a (hparts.1 hur).2.1 with
              | intro t ht =>
                exact ⟨t, ht.1, ht.2.1, ht.2.2.1, T.lt.p_first _ _ _ _ _ _ ht.2.2.2⟩
            · have hr0u : r0 < u := by
                cases T.lt_total r0 u with
                | inl hlt => exact hlt
                | inr hrest =>
                  cases hrest with
                  | inl hlt => exact False.elim (hur (Or.inl hlt))
                  | inr heq => exact False.elim (hur (Or.inr heq.symm))
              have huIndex := lt_of_le_of_lt_thm T u l (P l Z Z) hul (T.first_lt l Z Z)
              refine ⟨u, hu, huIndex, T.GBound_self u k hu, ?_⟩
              exact T.lt.p_first _ _ _ _ _ _ (lt_of_lt_of_le_thm T r0 u _ hr0u
                (T.input_le_fund_omega a l ha hadom u huIndex))
        | One => rw [hbdom] at hd; cases hd
        | ω => rw [hbdom] at hd; cases hd
        | Ω m =>
          rw [hbdom] at hd
          change (if a < m then Dom.ω else Dom.Ω m) = Dom.Ω l at hd
          by_cases ham : a < m
          · rw [ite_eq_left ham] at hd; cases hd
          · rw [ite_eq_right ham] at hd
            cases hd
            change ∃ t, T.isNF t ∧ t < P l Z Z ∧ T.GBound u t k ∧
              P r0 r1 r2 < (if a < l then
                P a (T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) t)) Z
                else P a (T.fund b t) Z)
            have hua := partial_order.trans u l a hul (T.le_of_not_lt a l ham)
            cases hrs with
            | p_first _ _ _ _ _ _ h0 =>
              refine ⟨Z, T.isNF.z, T.lt.Z_lt_P l Z Z, T.GBound_zero u k, ?_⟩
              rw [ite_eq_right ham]
              exact T.lt.p_first _ _ _ _ _ _ h0
            | p_second _ _ _ _ _ h1 =>
              cases ih1 l hbdom hul r1 hcomponents.2.1 h1 (hparts.1 hua).2.2 with
              | intro t ht =>
                refine ⟨t, ht.1, ht.2.1, ht.2.2.1, ?_⟩
                rw [ite_eq_right ham]
                exact T.lt.p_second _ _ _ _ _ ht.2.2.2
            | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
      · rw [T.dom, ite_eq_right hcZ] at hd
        conv =>
          enter [1, t, 2, 2, 2]
          rw [T.fund, ite_eq_right hcZ]
        cases hrs with
        | p_first _ _ _ _ _ _ h0 =>
          exact ⟨Z, T.isNF.z, T.lt.Z_lt_P l Z Z, T.GBound_zero u k,
            T.lt.p_first _ _ _ _ _ _ h0⟩
        | p_second _ _ _ _ _ h1 =>
          exact ⟨Z, T.isNF.z, T.lt.Z_lt_P l Z Z, T.GBound_zero u k,
            T.lt.p_second _ _ _ _ _ h1⟩
        | p_third _ _ _ _ h2 =>
          cases ih2 l hd hul r2 hcomponents.2.2 h2 hparts.2 with
          | intro t ht =>
            exact ⟨t, ht.1, ht.2.1, ht.2.2.1, T.lt.p_third _ _ _ _ ht.2.2.2⟩

theorem T.sequence_le_of_step (f : Nat → T) (hstep : ∀ n, f n < f (n + 1))
    (i j : Nat) (hij : i ≤ j) : f i ≤ f j := by
  induction hij with
  | refl => exact Or.inr rfl
  | @step j hle ih =>
    exact Or.inl (lt_of_le_of_lt_thm T (f i) (f j) (f (j + 1)) ih (hstep j))

theorem T.list_bound_sequence (xs : List T) (f : Nat → T)
    (hmono : ∀ i j, i ≤ j → f i ≤ f j)
    (hcover : ∀ x, x ∈ xs → ∃ n, x < f n) : ∃ n, ∀ x, x ∈ xs → x < f n := by
  induction xs with
  | nil =>
    refine ⟨0, ?_⟩
    intro x hx
    exact False.elim (List.not_mem_nil hx)
  | cons a xs ih =>
    cases hcover a List.mem_cons_self with
    | intro na hna =>
      have htail : ∀ x, x ∈ xs → ∃ n, x < f n := by
        intro x hx
        exact hcover x (List.mem_cons_of_mem a hx)
      cases ih htail with
      | intro nt hnt =>
        refine ⟨na + nt, ?_⟩
        intro x hx
        cases List.mem_cons.mp hx with
        | inl heq =>
          rw [heq]
          exact lt_of_lt_of_le_thm T a (f na) (f (na + nt)) hna
            (hmono na (na + nt) (Nat.le_add_right na nt))
        | inr hxt =>
          exact lt_of_lt_of_le_thm T x (f nt) (f (na + nt)) (hnt x hxt)
            (hmono nt (na + nt) (Nat.le_add_left nt na))

theorem T.lt_collapse_of_GBound (l t k : T) (hl : T.dom l = .One)
    (ht : t < P l Z Z) (hG : T.GBound (T.fund l Z) t k) :
    t < P (T.fund l Z) k Z := by
  cases t with
  | Z => exact T.lt.Z_lt_P _ k Z
  | P a b c =>
    have hal : a < l := by
      cases ht with
      | p_first _ _ _ _ _ _ h0 => exact h0
      | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
      | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
    cases (T.fund_one_properties l hl).2.2.1 a hal with
    | inl hlt => exact T.lt.p_first _ _ _ _ _ _ hlt
    | inr heq =>
      cases heq
      have hb := (((T.GBound_P (T.fund l Z) (T.fund l Z) b c k).mp hG).1 (Or.inr rfl)).1
      exact T.lt.p_second _ _ _ _ _ hb

/-- The iterates used in a collapsing clause dominate every normal term with bounded support. -/
theorem T.collapsing_iterates_cofinal (b l u : T) (hb : T.isNF b)
    (hd : T.dom b = .Ω l) (hul : u < l) (r : T)
    (hr : T.isNF r) (hrb : r < b) (hGr : T.GBound u r b) :
    ∃ n, r < T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n)) := by
  let F := fun x => P (T.fund l Z) (T.fund b x) Z
  let xs := fun n => T.iter F (T.ofNat n)
  let bs := fun n => T.fund b (xs n)
  have hlNF := T.dom_omega_index_isNF b l hb hd
  have hlone := T.dom_omega_index_one b l hd
  have hlne : l ≠ Z := by intro heq; rw [heq] at hlone; cases hlone
  have hlpNF := T.fund_one_isNF l hlNF hlone Z
  have hlplt := T.fund_lt_of_domain l Z hlne (fun m _ => T.lt.Z_lt_P m Z Z)
  have hulple := (T.fund_one_properties l hlone).2.2.1 u hul
  have xs_step : ∀ n, xs n < xs (n + 1) := by
    intro n
    induction n with
    | zero => exact T.lt.Z_lt_P _ _ Z
    | succ n ih =>
      exact T.lt.p_second _ _ _ _ _ (T.fund_omega_strict b l hd (xs n) (xs (n + 1)) ih)
  have bs_step : ∀ n, bs n < bs (n + 1) := by
    intro n
    exact T.fund_omega_strict b l hd (xs n) (xs (n + 1)) (xs_step n)
  have bs_mono := T.sequence_le_of_step bs bs_step
  have xs_bound : ∀ n, xs n < P l Z Z := by
    intro n
    cases n with
    | zero => exact T.lt.Z_lt_P l Z Z
    | succ n => exact T.lt.p_first _ _ _ _ _ _ hlplt
  have bs_one_pos : Z < bs 1 :=
    lt_of_lt_of_le_thm T Z (xs 1) (bs 1) (xs_step 0)
      (T.input_le_fund_omega b l hb hd (xs 1) (xs_bound 1))
  have cover : ∀ q, T.isNF q → q < b → T.GBound u q b → ∃ n, q < bs n := by
    intro q hq hqb hGq
    induction q using (measure T.size).wf.induction with
    | h q ih =>
      have hmembers : ∀ x, x ∈ T.G u q → ∃ n, x < bs n := by
        intro x hx
        have hp := T.mem_G_properties u q x hq hx
        exact ih x hp.2 hp.1 (hGq x hx) (T.GBound_mem u q x b hGq hx)
      cases T.list_bound_sequence (T.G u q) bs bs_mono hmembers with
      | intro n hn =>
        have hGnext : T.GBound u q (bs (n + 1)) := by
          intro x hx
          exact T.lt_trans _ _ _ (hn x hx) (bs_step n)
        have hpos : Z < bs (n + 1) :=
          lt_of_lt_of_le_thm T Z (bs 1) (bs (n + 1)) bs_one_pos
            (bs_mono 1 (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
        have hGpred := T.GBound_index_mono q u (T.fund l Z) (bs (n + 1)) hulple hGnext
        cases T.fund_omega_cofinal_support b hb l (T.fund l Z) (bs (n + 1)) hd
            hlpNF (Or.inl hlplt) hpos q hq hqb hGpred with
        | intro t ht =>
          have htx : t < xs (n + 2) :=
            T.lt_collapse_of_GBound l t (bs (n + 1)) hlone ht.2.1 ht.2.2.1
          exact ⟨n + 2, T.lt_trans _ _ _ ht.2.2.2 (T.fund_omega_strict b l hd t (xs (n + 2)) htx)⟩
  exact cover r hr hrb hGr

theorem T.fund_collapsing_principal_cofinal (a b l r : T) (hs : T.isNF (P a b Z))
    (hd : T.dom b = .Ω l) (hal : a < l) (hr : T.isNF r) (hrs : r < P a b Z) :
    ∃ n, r ≤ T.fund (P a b Z) (T.ofNat n) := by
  have hb := (T.isNF_components a b Z hs).2.1
  have heq : ∀ n, T.fund (P a b Z) (T.ofNat n) =
      P a (T.fund b (T.iter (fun x => P (T.fund l Z) (T.fund b x) Z) (T.ofNat n))) Z := by
    intro n
    rw [T.fund, ite_eq_left rfl, hd]
    change (if a < l then _ else _) = _
    rw [ite_eq_left hal]
  cases r with
  | Z =>
    refine ⟨0, ?_⟩
    rw [heq]
    exact T.Z_le _
  | P r0 r1 r2 =>
    cases hrs with
    | p_first _ _ _ _ _ _ h0 =>
      refine ⟨0, ?_⟩
      rw [heq]
      exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
    | p_second _ _ _ _ _ h1 =>
      have hr1 := (T.isNF_components a r1 r2 hr).2.1
      have hG : T.GBound a r1 b := by
        cases hr with
        | p _ _ _ h0 h1' h2 hreg hhead =>
          intro x hx
          exact T.lt_trans x r1 b (hreg x hx) h1
      cases T.collapsing_iterates_cofinal b l a hb hd hal r1 hr1 h1 hG with
      | intro n hn =>
        refine ⟨n, ?_⟩
        rw [heq]
        exact Or.inl (T.lt.p_second _ _ _ _ _ hn)
    | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)

theorem T.fund_nonomega_cofinal (s : T) (hs : T.isNF s)
    (hd : ∀ l, T.dom s ≠ .Ω l) (r : T) (hr : T.isNF r) (hrs : r < s) :
    ∃ n, r ≤ T.fund s (T.ofNat n) := by
  induction hs generalizing r with
  | z => exact False.elim (lt_Z_inv r hrs)
  | p a b c ha hb hc hreg hhead ih0 ih1 ih2 =>
    have hs := T.isNF.p a b c ha hb hc hreg hhead
    by_cases hcZ : c = Z
    · cases hcZ
      cases hbdom : T.dom b with
      | Zero =>
        have hbZ := T.dom_eq_zero b hbdom
        cases hbZ
        cases hadom : T.dom a with
        | Zero =>
          have haZ := T.dom_eq_zero a hadom
          cases haZ
          have hrZ := T.lt_one_inv r hrs
          cases hrZ
          refine ⟨0, ?_⟩
          rw [T.fund, ite_eq_left rfl]
          exact Or.inr rfl
        | One =>
          apply False.elim
          apply hd a
          rw [T.dom, ite_eq_left rfl]
          change (match T.dom a with
            | .Zero => Dom.One | .One => Dom.Ω a | .ω => Dom.ω | .Ω m => Dom.Ω m) = _
          rw [hadom]
        | ω =>
          have heq : ∀ n, T.fund (P a Z Z) (T.ofNat n) = P (T.fund a (T.ofNat n)) Z Z := by
            intro n
            rw [T.fund, ite_eq_left rfl, hbdom, hadom]
          cases r with
          | Z => refine ⟨0, ?_⟩; rw [heq]; exact T.Z_le _
          | P r0 r1 r2 =>
            have hr0 := (T.isNF_components r0 r1 r2 hr).1
            have hr0a : r0 < a := by
              cases hrs with
              | p_first _ _ _ _ _ _ h0 => exact h0
              | p_second _ _ _ _ _ h1 => exact False.elim (lt_Z_inv _ h1)
              | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
            have hanot : T.dom a ≠ .One := by intro h; rw [hadom] at h; cases h
            have had : ∀ l, T.dom a ≠ .Ω l := by intro l h; rw [hadom] at h; cases h
            have hrplus := T.add_one_lt_of_dom_ne_one a r0 hanot hr0a
            cases ih0 had (r0 + P Z Z Z) (T.add_one_isNF r0 hr0) hrplus with
            | intro n hn =>
              refine ⟨n, ?_⟩
              rw [heq]
              exact Or.inl (T.lt.p_first _ _ _ _ _ _
                (lt_of_lt_of_le_thm T r0 (r0 + P Z Z Z) _ (T.lt_add_one r0) hn))
        | Ω l =>
          apply False.elim
          apply hd l
          rw [T.dom, ite_eq_left rfl]
          change (match T.dom a with
            | .Zero => Dom.One | .One => Dom.Ω a | .ω => Dom.ω | .Ω m => Dom.Ω m) = _
          rw [hadom]
      | One => exact T.fund_principal_successor_cofinal a b r hbdom hr hrs
      | ω =>
        have heq : ∀ n, T.fund (P a b Z) (T.ofNat n) = P a (T.fund b (T.ofNat n)) Z := by
          intro n
          rw [T.fund, ite_eq_left rfl, hbdom]
        cases r with
        | Z => refine ⟨0, ?_⟩; rw [heq]; exact T.Z_le _
        | P r0 r1 r2 =>
          cases hrs with
          | p_first _ _ _ _ _ _ h0 =>
            refine ⟨0, ?_⟩
            rw [heq]
            exact Or.inl (T.lt.p_first _ _ _ _ _ _ h0)
          | p_second _ _ _ _ _ h1 =>
            have hr1 := (T.isNF_components a r1 r2 hr).2.1
            have hbnot : T.dom b ≠ .One := by intro h; rw [hbdom] at h; cases h
            have hbd : ∀ l, T.dom b ≠ .Ω l := by intro l h; rw [hbdom] at h; cases h
            have hrplus := T.add_one_lt_of_dom_ne_one b r1 hbnot h1
            cases ih1 hbd (r1 + P Z Z Z) (T.add_one_isNF r1 hr1) hrplus with
            | intro n hn =>
              refine ⟨n, ?_⟩
              rw [heq]
              exact Or.inl (T.lt.p_second _ _ _ _ _
                (lt_of_lt_of_le_thm T r1 (r1 + P Z Z Z) _ (T.lt_add_one r1) hn))
          | p_third _ _ _ _ h2 => exact False.elim (lt_Z_inv _ h2)
      | Ω l =>
        by_cases hal : a < l
        · exact T.fund_collapsing_principal_cofinal a b l r hs hbdom hal hr hrs
        · apply False.elim
          apply hd l
          rw [T.dom, ite_eq_left rfl, hbdom]
          change (if a < l then Dom.ω else Dom.Ω l) = Dom.Ω l
          rw [ite_eq_right hal]
    · apply T.fund_nonzero_tail_cofinal a b c r hcZ
      · apply ih2
        intro l hl
        apply hd l
        rw [T.dom, ite_eq_right hcZ]
        exact hl
      · exact hr
      · exact hrs

theorem T.fund_cofinal_below_omega_one (s r : T) (hs : T.isNF s) (hr : T.isNF r)
    (hb : s < P (P Z Z Z) Z Z) (hrs : r < s) :
    ∃ n, r ≤ T.fund s (T.ofNat n) :=
  T.fund_nonomega_cofinal s hs (T.dom_ne_omega_below_omega_one s hs hb) r hr hrs


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

theorem T.GBound_or_failure (u s b : T) :
    T.GBound u s b ∨ ∃ x, x ∈ T.G u s ∧ b ≤ x := by
  have check : ∀ xs : List T,
      (∀ x, x ∈ xs → x < b) ∨ ∃ x, x ∈ xs ∧ b ≤ x := by
    intro xs
    induction xs with
    | nil =>
      apply Or.inl
      intro x hx
      exact False.elim (List.not_mem_nil hx)
    | cons a xs ih =>
      by_cases hab : a < b
      · cases ih with
        | inl htail =>
          apply Or.inl
          intro x hx
          cases List.mem_cons.mp hx with
          | inl heq => rw [heq]; exact hab
          | inr hxt => exact htail x hxt
        | inr hbad =>
          cases hbad with
          | intro x hx => exact Or.inr ⟨x, List.mem_cons_of_mem a hx.1, hx.2⟩
      · exact Or.inr ⟨a, List.mem_cons_self, T.le_of_not_lt a b hab⟩
  exact check (T.G u s)

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
        cases T.GBound_or_failure u c b with
        | inl hgood => exact ⟨c, hbc, Or.inl hca, hgood⟩
        | inr hbad =>
          cases hbad with
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


theorem T.OT_characterization_of_wellFounded_and_fundamental_properties
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1)
    (hclosed : ∀ s, T.isNF s → s < P (P Z Z Z) Z Z →
      ∀ n, T.isNF (T.fund s (T.ofNat n)))
    (s : T) :
    T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z := by
  apply Iff.intro
  · intro hs
    induction hs with
    | base n => exact And.intro (T.base_isNF n) (T.base_lt_omega_one n)
    | step t ht n ih =>
      apply And.intro (hclosed t ih.1 ih.2 n)
      by_cases heq : t = Z
      · rw [heq, T.fund_Z]
        exact T.lt.Z_lt_P (P Z Z Z) Z Z
      · exact T.lt_trans _ _ _ (T.fund_ofNat_lt t n heq) ih.2
  · intro hs
    have downward : ∀ x : T.NF, T.isOT x.1 → x.1 < P (P Z Z Z) Z Z →
        ∀ r, T.isNF r → r ≤ x.1 → T.isOT r := by
      intro x
      induction x using hwf.induction with
      | h x ih =>
        intro hx hxbound r hr hrx
        cases hrx with
        | inr heq =>
          cases heq
          exact hx
        | inl hrx =>
          have hne : x.1 ≠ Z := by
            intro heq
            rw [heq] at hrx
            exact lt_Z_inv r hrx
          cases T.fund_cofinal_below_omega_one x.1 r x.2 hr hxbound hrx with
          | intro n hn =>
            let y : T.NF := ⟨T.fund x.1 (T.ofNat n), hclosed x.1 x.2 hxbound n⟩
            have hyx : y.1 < x.1 := T.fund_ofNat_lt x.1 n hne
            exact ih y hyx (T.isOT.step x.1 hx n)
              (T.lt_trans _ _ _ hyx hxbound) r hr hn
    cases T.base_cofinal_below_omega_one s hs.2 with
    | intro n hn =>
      exact downward ⟨P Z (T.LF n) Z, T.base_isNF n⟩ (T.isOT.base n)
        (T.base_lt_omega_one n) s hs.1 (Or.inl hn)

theorem T.OT_characterization_of_fundamental_properties
    (hclosed : ∀ s, T.isNF s → s < P (P Z Z Z) Z Z →
      ∀ n, T.isNF (T.fund s (T.ofNat n)))
    (s : T) :
    T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z :=
  T.OT_characterization_of_wellFounded_and_fundamental_properties
    T.NF_is_wellfounded hclosed s

/-- A constructive proof of well-foundedness suffices for the characterization. -/
theorem T.OT_is_NF_of_wellFounded
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1)
    (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z := by
  exact T.OT_characterization_of_wellFounded_and_fundamental_properties hwf
    (fun t ht _ n => T.fund_ofNat_isNF t ht n) s

theorem T.OT_is_NF (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z :=
  T.OT_is_NF_of_wellFounded T.NF_is_wellfounded s

def T.OT := { s : T // T.isOT s }

theorem T.OT_wellFounded_of_NF_wellFounded
    (hwf : WellFounded fun x y : T.NF => x.1 < y.1) :
    WellFounded fun x y : T.OT => x.1 < y.1 := by
  let toNF : T.OT → T.NF := fun x => ⟨x.1, ((T.OT_is_NF_of_wellFounded hwf x.1).mp x.2).1⟩
  exact InvImage.wf toNF hwf

theorem T.OT_is_wellfounded : WellFounded fun x y : T.OT => x.1 < y.1 :=
  T.OT_wellFounded_of_NF_wellFounded T.NF_is_wellfounded
