import Multi.order

inductive T where
| Z
| P (s0 s1 s2 s3 : T)
deriving DecidableEq

open T

inductive T.lt : T → T → Prop where
| Z_lt_P (t0 t1 t2 t3 : T) :
  T.lt Z (P t0 t1 t2 t3)
| p_first (s0 s1 s2 s3 t0 t1 t2 t3 : T) (h : T.lt s0 t0) :
  T.lt (P s0 s1 s2 s3) (P t0 t1 t2 t3)
| p_second (s0 s1 s2 s3 t1 t2 t3 : T) (h : T.lt s1 t1) :
  T.lt (P s0 s1 s2 s3) (P s0 t1 t2 t3)
| p_third (s0 s1 s2 s3 t2 t3 : T) (h : T.lt s2 t2) :
  T.lt (P s0 s1 s2 s3) (P s0 s1 t2 t3)
| p_fourth (s0 s1 s2 s3 t3 : T) (h : T.lt s3 t3) :
  T.lt (P s0 s1 s2 s3) (P s0 s1 s2 t3)

instance : LT T where
  lt a b := T.lt a b

theorem lt_Z_Z_inv (h : Z < Z) : False := by
  cases h

theorem lt_P_Z_inv (s0 s1 s2 s3 : T) (h : (P s0 s1 s2 s3) < Z) : False := by
  cases h

theorem lt_Z_inv (a : T) (h : a < Z) : False := by
  cases a with
  | Z => exact lt_Z_Z_inv h
  | P a0 a1 a2 a3 => exact lt_P_Z_inv a0 a1 a2 a3 h

theorem lt_inv (s0 s1 s2 s3 t0 t1 t2 t3 : T) (h : P s0 s1 s2 s3 < P t0 t1 t2 t3) :
  s0 < t0 ∨ (s0 = t0 ∧ s1 < t1) ∨ (s0 = t0 ∧ s1 = t1 ∧ s2 < t2) ∨ (s0 = t0 ∧ s1 = t1 ∧ s2 = t2 ∧ s3 < t3) := by
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
    apply Or.inl
    apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · exact h_lt
  case p_fourth h_lt =>
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply And.intro
    · rfl
    · apply And.intro
      · rfl
      · apply And.intro
        · rfl
        · exact h_lt

def T.decLt (a b : T) : Decidable (a < b) :=
  match a, b with
  | Z, Z => isFalse lt_Z_Z_inv
  | Z, P t0 t1 t2 t3 => isTrue (T.lt.Z_lt_P t0 t1 t2 t3)
  | P s0 s1 s2 s3, Z => isFalse (lt_P_Z_inv s0 s1 s2 s3)
  | P s0 s1 s2 s3, P t0 t1 t2 t3 =>
    match T.decLt s0 t0 with
    | isTrue h0 => isTrue (T.lt.p_first s0 s1 s2 s3 t0 t1 t2 t3 h0)
    | isFalse hn0 =>
      if heq0 : s0 = t0 then
        match t0, heq0 with
        | _, rfl =>
          match T.decLt s1 t1 with
          | isTrue h1 => isTrue (T.lt.p_second s0 s1 s2 s3 t1 t2 t3 h1)
          | isFalse hn1 =>
            if heq1 : s1 = t1 then
              match t1, heq1 with
              | _, rfl =>
                match T.decLt s2 t2 with
                | isTrue h2 => isTrue (T.lt.p_third s0 s1 s2 s3 t2 t3 h2)
                | isFalse hn2 =>
                  if heq2 : s2 = t2 then
                    match t2, heq2 with
                    | _, rfl =>
                      match T.decLt s3 t3 with
                      | isTrue h3 => isTrue (T.lt.p_fourth s0 s1 s2 s3 t3 h3)
                      | isFalse hn3 =>
                        isFalse (fun h =>
                            match lt_inv s0 s1 s2 s3 s0 s1 s2 t3 h with
                            | Or.inl h_lt => hn0 h_lt
                            | Or.inr (Or.inl h_and) => hn1 h_and.2
                            | Or.inr (Or.inr (Or.inl h_and)) => hn2 h_and.2.2
                            | Or.inr (Or.inr (Or.inr h_and)) => hn3 h_and.2.2.2
                          )
                  else
                    isFalse (fun h =>
                        match lt_inv s0 s1 s2 s3 s0 s1 t2 t3 h with
                        | Or.inl h_lt => hn0 h_lt
                        | Or.inr (Or.inl h_and) => hn1 h_and.2
                        | Or.inr (Or.inr (Or.inl h_and)) => hn2 h_and.2.2
                        | Or.inr (Or.inr (Or.inr h_and)) => heq2 h_and.2.2.1
                      )
            else
              isFalse (fun h =>
                match lt_inv s0 s1 s2 s3 s0 t1 t2 t3 h with
                | Or.inl h_lt => hn0 h_lt
                | Or.inr (Or.inl h_and) => hn1 h_and.2
                | Or.inr (Or.inr (Or.inl h_and)) => heq1 h_and.2.1
                | Or.inr (Or.inr (Or.inr h_and)) => heq1 h_and.2.1
              )
      else
        isFalse (fun h =>
          match lt_inv s0 s1 s2 s3 t0 t1 t2 t3 h with
          | Or.inl h_lt => hn0 h_lt
          | Or.inr (Or.inl h_and) => heq0 h_and.1
          | Or.inr (Or.inr (Or.inl h_and)) => heq0 h_and.1
          | Or.inr (Or.inr (Or.inr h_and)) => heq0 h_and.1
        )

instance (a b : T) : Decidable (a < b) :=
  T.decLt a b

theorem T.lt_irrefl (a : T) : ¬ a < a := by
  induction a with
  | Z =>
    intro h
    exact lt_Z_Z_inv h
  | P s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
    intro h
    have h_inv := lt_inv s0 s1 s2 s3 s0 s1 s2 s3 h
    cases h_inv with
    | inl h_lt =>
      exact ih0 h_lt
    | inr h_or0 =>
      cases h_or0 with
      | inl h_lt =>
        exact ih1 h_lt.2
      | inr h_or1 =>
        cases h_or1 with
        | inl h_lt =>
          exact ih2 h_lt.2.2
        | inr h_and =>
          exact ih3 h_and.2.2.2

theorem T.lt_trans (a : T) : ∀ b c : T, a < b → b < c → a < c := by
  induction a with
  | Z =>
    intro b c hab hbc
    cases c with
    | Z => exact False.elim (lt_Z_inv b hbc)
    | P c0 c1 c2 c3 => exact T.lt.Z_lt_P c0 c1 c2 c3
  | P a0 a1 a2 a3 ih0 ih1 ih2 ih3 =>
    intro b c hab hbc
    cases b with
    | Z => exact False.elim (lt_P_Z_inv a0 a1 a2 a3 hab)
    | P b0 b1 b2 b3 =>
      cases c with
      | Z => exact False.elim (lt_P_Z_inv b0 b1 b2 b3 hbc)
      | P c0 c1 c2 c3 =>
        cases hab with
        | p_first _ _ _ _ _ _ _ _ hab0 =>
          cases hbc with
          | p_first _ _ _ _ _ _ _ _ hbc0 =>
            exact T.lt.p_first _ _ _ _ _ _ _ _ (ih0 _ _ hab0 hbc0)
          | p_second _ _ _ _ _ _ _ hbc1 => exact T.lt.p_first _ _ _ _ _ _ _ _ hab0
          | p_third _ _ _ _ _ _ hbc2 => exact T.lt.p_first _ _ _ _ _ _ _ _ hab0
          | p_fourth _ _ _ _ _ hbc3 => exact T.lt.p_first _ _ _ _ _ _ _ _ hab0
        | p_second _ _ _ _ _ _ _ hab1 =>
          cases hbc with
          | p_first _ _ _ _ _ _ _ _ hbc0 => exact T.lt.p_first _ _ _ _ _ _ _ _ hbc0
          | p_second _ _ _ _ _ _ _ hbc1 =>
            exact T.lt.p_second _ _ _ _ _ _ _ (ih1 _ _ hab1 hbc1)
          | p_third _ _ _ _ _ _ hbc2 => exact T.lt.p_second _ _ _ _ _ _ _ hab1
          | p_fourth _ _ _ _ _ hbc3 => exact T.lt.p_second _ _ _ _ _ _ _ hab1
        | p_third _ _ _ _ _ _ hab2 =>
          cases hbc with
          | p_first _ _ _ _ _ _ _ _ hbc0 => exact T.lt.p_first _ _ _ _ _ _ _ _ hbc0
          | p_second _ _ _ _ _ _ _ hbc1 => exact T.lt.p_second _ _ _ _ _ _ _ hbc1
          | p_third _ _ _ _ _ _ hbc2 =>
            exact T.lt.p_third _ _ _ _ _ _ (ih2 _ _ hab2 hbc2)
          | p_fourth _ _ _ _ _ hbc3 => exact T.lt.p_third _ _ _ _ _ _ hab2
        | p_fourth _ _ _ _ _ hab3 =>
          cases hbc with
          | p_first _ _ _ _ _ _ _ _ hbc0 => exact T.lt.p_first _ _ _ _ _ _ _ _ hbc0
          | p_second _ _ _ _ _ _ _ hbc1 => exact T.lt.p_second _ _ _ _ _ _ _ hbc1
          | p_third _ _ _ _ _ _ hbc2 => exact T.lt.p_third _ _ _ _ _ _ hbc2
          | p_fourth _ _ _ _ _ hbc3 =>
            exact T.lt.p_fourth _ _ _ _ _ (ih3 _ _ hab3 hbc3)

theorem T.lt_asymm {a b : T} (h : a < b) : ¬ (b < a) := by
  intro hba
  have htrans := T.lt_trans a b a h hba
  exact T.lt_irrefl a htrans

theorem T.lt_total (a b : T) : a < b ∨ b < a ∨ a = b := by
  induction a generalizing b with
  | Z =>
    cases b with
    | Z => exact Or.inr (Or.inr rfl)
    | P b0 b1 b2 b3 => exact Or.inl (T.lt.Z_lt_P b0 b1 b2 b3)
  | P a0 a1 a2 a3 ih0 ih1 ih2 ih3 =>
    cases b with
    | Z => exact Or.inr (Or.inl (T.lt.Z_lt_P a0 a1 a2 a3))
    | P b0 b1 b2 b3 =>
      cases ih0 b0 with
      | inl h0 => exact Or.inl (T.lt.p_first _ _ _ _ _ _ _ _ h0)
      | inr h0 =>
        cases h0 with
        | inl h0 => exact Or.inr (Or.inl (T.lt.p_first _ _ _ _ _ _ _ _ h0))
        | inr e0 =>
          cases e0
          cases ih1 b1 with
          | inl h1 => exact Or.inl (T.lt.p_second _ _ _ _ _ _ _ h1)
          | inr h1 =>
            cases h1 with
            | inl h1 => exact Or.inr (Or.inl (T.lt.p_second _ _ _ _ _ _ _ h1))
            | inr e1 =>
              cases e1
              cases ih2 b2 with
              | inl h2 => exact Or.inl (T.lt.p_third _ _ _ _ _ _ h2)
              | inr h2 =>
                cases h2 with
                | inl h2 => exact Or.inr (Or.inl (T.lt.p_third _ _ _ _ _ _ h2))
                | inr e2 =>
                  cases e2
                  cases ih3 b3 with
                  | inl h3 => exact Or.inl (T.lt.p_fourth _ _ _ _ _ h3)
                  | inr h3 =>
                    cases h3 with
                    | inl h3 => exact Or.inr (Or.inl (T.lt.p_fourth _ _ _ _ _ h3))
                    | inr e3 =>
                      cases e3
                      exact Or.inr (Or.inr rfl)

instance : strict_partial_order T where
  irrefl a := T.lt_irrefl a
  trans a b c hf hs := T.lt_trans a b c hf hs

instance : strict_linear_order T where
  total a b := T.lt_total a b

theorem T.Z_le (s : T) : Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P s0 s1 s2 s3 =>
    apply Or.inl
    exact T.lt.Z_lt_P s0 s1 s2 s3

def T.add : T → T → T
| Z, t => t
| s, Z => s
| P s0 s1 s2 s3, t =>
  P s0 s1 s2 (s3.add t)

instance : Add T where
  add := T.add

def T.mul : T → T → T
| _, Z => Z
| a, P _ _ _ m2 => mul a m2 + a

def T.iter (F : T → T) : T → T
| Z => Z
| P _ _ _ m2 => F (iter F m2)

def T.size : T → Nat
| Z => 0
| P t0 t1 t2 t3 => t0.size + t1.size + t2.size + t3.size + 1

theorem T.size_P (s0 s1 s2 s3 : T) : (P s0 s1 s2 s3).size = s0.size + s1.size + s2.size + s3.size + 1 := rfl

theorem T.size_lt_size_P_first (s0 s1 s2 s3 : T) : s0.size < (P s0 s1 s2 s3).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  rw [Nat.add_assoc _ _ _]
  rw [Nat.add_assoc _ _ _]
  exact Nat.le_add_right _ _

theorem T.size_lt_size_P_second (s0 s1 s2 s3 : T) : s1.size < (P s0 s1 s2 s3).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  rw [Nat.add_assoc _ _ _]
  rw [Nat.add_comm s0.size s1.size]
  rw [Nat.add_assoc _ _ _]
  exact Nat.le_add_right _ _

theorem T.size_lt_size_P_third (s0 s1 s2 s3 : T) : s2.size < (P s0 s1 s2 s3).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  rw [Nat.add_assoc _ _ _]
  rw [Nat.add_comm s2.size s3.size]
  rw [← Nat.add_assoc _ _ _]
  exact Nat.le_add_left _ _

theorem T.size_lt_size_P_fourth (s0 s1 s2 s3 : T) : s3.size < (P s0 s1 s2 s3).size := by
  rw [T.size_P]
  apply Nat.lt_succ_of_le
  exact Nat.le_add_left _ _

inductive T.Dom where
| Zero
| One
| ω
| Ω (l0 l1 : T)
deriving DecidableEq

def T.dom (s : T) : Dom :=
  match s with
  | Z => .Zero
  | P s0 s1 s2 s3 =>
    if s3 = Z then
      match T.dom s2 with
      | .Zero =>
        match T.dom s1 with
        | .Zero =>
          match T.dom s0 with
          | .Zero => .One
          | .One => .Ω s0 Z
          | .ω => .ω
          | .Ω l0 l1 => .Ω l0 l1
        | .One => .Ω s0 s1
        | .ω => .ω
        | .Ω l0 l1 =>
          if P s0 s1 Z Z < P l0 l1 Z Z then
            .ω
          else .Ω l0 l1
      | .One => .ω
      | .ω => .ω
      | .Ω l0 l1 =>
        if P s0 s1 s2 Z < P l0 l1 Z Z then
          .ω
        else .Ω l0 l1
    else T.dom s3

theorem T.dom_omega_size (s l0 l1 : T) (h : T.dom s = .Ω l0 l1) :
    l0.size < s.size ∧ l1.size < s.size := by
  induction s generalizing l0 l1 with
  | Z =>
    change Dom.Zero = Dom.Ω l0 l1 at h
    cases h
  | P s0 s1 s2 s3 ih0 ih1 ih2 ih3 =>
    rw [T.dom] at h
    split at h
    · cases h2 : T.dom s2 with
      | Zero =>
        rw [h2] at h
        cases h1 : T.dom s1 with
        | Zero =>
          rw [h1] at h
          cases h0 : T.dom s0 with
          | Zero =>
            rw [h0] at h
            cases h
          | One =>
            rw [h0] at h
            cases h
            exact And.intro (T.size_lt_size_P_first s0 s1 s2 s3)
              (Nat.lt_succ_of_le (Nat.zero_le _))
          | ω =>
            rw [h0] at h
            cases h
          | Ω m0 m1 =>
            rw [h0] at h
            cases h
            have hs := ih0 _ _ h0
            exact And.intro
              (Nat.lt_trans hs.1 (T.size_lt_size_P_first s0 s1 s2 s3))
              (Nat.lt_trans hs.2 (T.size_lt_size_P_first s0 s1 s2 s3))
        | One =>
          rw [h1] at h
          cases h
          exact And.intro (T.size_lt_size_P_first s0 s1 s2 s3)
            (T.size_lt_size_P_second s0 s1 s2 s3)
        | ω =>
          rw [h1] at h
          cases h
        | Ω m0 m1 =>
          rw [h1] at h
          change (if P s0 s1 Z Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) =
            Dom.Ω l0 l1 at h
          split at h
          · cases h
          · cases h
            have hs := ih1 _ _ h1
            exact And.intro
              (Nat.lt_trans hs.1 (T.size_lt_size_P_second s0 s1 s2 s3))
              (Nat.lt_trans hs.2 (T.size_lt_size_P_second s0 s1 s2 s3))
      | One =>
        rw [h2] at h
        cases h
      | ω =>
        rw [h2] at h
        cases h
      | Ω m0 m1 =>
        rw [h2] at h
        change (if P s0 s1 s2 Z < P m0 m1 Z Z then Dom.ω else Dom.Ω m0 m1) =
          Dom.Ω l0 l1 at h
        split at h
        · cases h
        · cases h
          have hs := ih2 _ _ h2
          exact And.intro
            (Nat.lt_trans hs.1 (T.size_lt_size_P_third s0 s1 s2 s3))
            (Nat.lt_trans hs.2 (T.size_lt_size_P_third s0 s1 s2 s3))
    · have hs := ih3 l0 l1 h
      exact And.intro
        (Nat.lt_trans hs.1 (T.size_lt_size_P_fourth s0 s1 s2 s3))
        (Nat.lt_trans hs.2 (T.size_lt_size_P_fourth s0 s1 s2 s3))

def T.fund (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 s3 =>
    if s3 = Z then
      match _h2 : T.dom s2 with
      | .Zero =>
        match _h1 : T.dom s1 with
        | .Zero =>
          match _h0 : T.dom s0 with
          | .Zero => Z
          | .One => t
          | .ω => P (T.fund s0 t) Z Z Z
          | .Ω _ _ => P (T.fund s0 t) Z Z Z
        | .One => t
        | .ω => P s0 (T.fund s1 t) Z Z
        | .Ω l0 l1 =>
          if P s0 s1 Z Z < P l0 l1 Z Z then
            if T.dom l1 = .One then
              let e' := T.fund l1 Z
              let F := fun x => P l0 e' (T.fund s1 x) Z
              P s0 (T.fund s1 (T.iter F t)) Z Z
            else
              let f' := T.fund l0 Z
              let F := fun x => P f' (T.fund s1 x) Z Z
              P s0 (T.fund s1 (T.iter F t)) Z Z
          else P s0 (T.fund s1 t) Z Z
      | .One => T.mul (P s0 s1 (T.fund s2 Z) Z) t
      | .ω => P s0 s1 (T.fund s2 t) Z
      | .Ω l0 l1 =>
        if P s0 s1 s2 Z < P l0 l1 Z Z then
          if T.dom l1 = .One then
            let e' := T.fund l1 Z
            let F := fun x => P l0 e' (T.fund s2 x) Z
            P s0 s1 (T.fund s2 (T.iter F t)) Z
          else
            let f' := T.fund l0 Z
            let F := fun x => P f' (T.fund s2 x) Z Z
            P s0 s1 (T.fund s2 (T.iter F t)) Z
        else P s0 s1 (T.fund s2 t) Z
    else P s0 s1 s2 (T.fund s3 t)
termination_by T.size s
decreasing_by
  · exact T.size_lt_size_P_first s0 s1 s2 s3
  · exact T.size_lt_size_P_first s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s1 l0 l1 _h1).2 (T.size_lt_size_P_second s0 s1 s2 s3)
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s1 l0 l1 _h1).1 (T.size_lt_size_P_second s0 s1 s2 s3)
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_second s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s2 l0 l1 _h2).2 (T.size_lt_size_P_third s0 s1 s2 s3)
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact Nat.lt_trans (T.dom_omega_size s2 l0 l1 _h2).1 (T.size_lt_size_P_third s0 s1 s2 s3)
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_third s0 s1 s2 s3
  · exact T.size_lt_size_P_fourth s0 s1 s2 s3

def T.LF (n : Nat) :=
  match n with
  | 0 => Z
  | n' + 1 => P (LF n') Z Z Z

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P Z Z Z (T.ofNat n)

inductive T.isOT : T → Prop where
| base (n : Nat) : T.isOT (P Z Z (T.LF n) Z)
| step (s : T) (hs : T.isOT s) (n : Nat) : T.isOT (T.fund s (T.ofNat n))

def T.OT := { s : T // T.isOT s }

