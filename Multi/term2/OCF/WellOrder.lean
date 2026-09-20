/-
Basic well-order constructions for the ordinal interpretation of term2.
Only Lean's core library is used.
-/

namespace OCF

universe u

structure WellOrder where
  Carrier : Type u
  lt : Carrier → Carrier → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace WellOrder

structure Iso (A B : WellOrder.{u}) where
  toFun : A.Carrier → B.Carrier
  invFun : B.Carrier → A.Carrier
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  lt_iff : ∀ a b, B.lt (toFun a) (toFun b) ↔ A.lt a b

def Iso.refl (A : WellOrder.{u}) : Iso A A where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

def Iso.trans {A B C : WellOrder.{u}} (e : Iso A B) (f : Iso B C) : Iso A C where
  toFun a := f.toFun (e.toFun a)
  invFun c := e.invFun (f.invFun c)
  left_inv a := by
    rw [f.left_inv, e.left_inv]
  right_inv c := by
    rw [e.right_inv, f.right_inv]
  lt_iff a b := Iff.trans (f.lt_iff (e.toFun a) (e.toFun b)) (e.lt_iff a b)

def Iso.symm {A B : WellOrder.{u}} (e : Iso A B) : Iso B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  lt_iff a b := by
    have h := e.lt_iff (e.invFun a) (e.invFun b)
    rw [e.right_inv a, e.right_inv b] at h
    exact h.symm

theorem Iso.injective {A B : WellOrder.{u}} (e : Iso A B) (a b : A.Carrier)
    (h : e.toFun a = e.toFun b) : a = b := by
  have he := congrArg e.invFun h
  rw [e.left_inv a, e.left_inv b] at he
  exact he

def below (A : WellOrder.{u}) (a : A.Carrier) : WellOrder.{u} where
  Carrier := { b : A.Carrier // A.lt b a }
  lt b c := A.lt b.1 c.1
  irrefl b := A.irrefl b.1
  trans b c d hbc hcd := A.trans b.1 c.1 d.1 hbc hcd
  total b c := by
    cases A.total b.1 c.1 with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (Subtype.ext h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf Subtype.val A.wellFounded

def Iso.below {A B : WellOrder.{u}} (e : Iso A B) (a : A.Carrier) :
    Iso (A.below a) (B.below (e.toFun a)) where
  toFun b := ⟨e.toFun b.1, (e.lt_iff b.1 a).mpr b.2⟩
  invFun b := ⟨e.invFun b.1, by
    apply (e.lt_iff (e.invFun b.1) a).mp
    rw [e.right_inv b.1]
    exact b.2⟩
  left_inv b := Subtype.ext (e.left_inv b.1)
  right_inv b := Subtype.ext (e.right_inv b.1)
  lt_iff b c := e.lt_iff b.1 c.1

def belowBelowIso (A : WellOrder.{u}) (a : A.Carrier) (b : (A.below a).Carrier) :
    Iso ((A.below a).below b) (A.below b.1) where
  toFun c := ⟨c.1.1, c.2⟩
  invFun c := ⟨⟨c.1, A.trans c.1 b.1 a c.2 b.2⟩, c.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

/-- A well-order is smaller if it is isomorphic to a proper initial segment. -/
def Below (A B : WellOrder.{u}) : Prop :=
  ∃ b : B.Carrier, Nonempty (Iso A (B.below b))

theorem Below.iso_right {A B C : WellOrder.{u}} (e : Iso B C) (h : Below A B) :
    Below A C := by
  cases h with
  | intro b hb =>
    cases hb with
    | intro f =>
      exact Exists.intro (e.toFun b) (Nonempty.intro (f.trans (e.below b)))

theorem Below.iso_left {A B C : WellOrder.{u}} (e : Iso A B) (h : Below B C) :
    Below A C := by
  cases h with
  | intro c hc =>
    cases hc with
    | intro f => exact Exists.intro c (Nonempty.intro (e.trans f))

theorem acc_of_iso {A B : WellOrder.{u}} (e : Iso A B) (h : Acc Below B) :
    Acc Below A := by
  induction h generalizing A with
  | intro B _ ih =>
    apply Acc.intro
    intro C hC
    exact ih C (Below.iso_right e hC) (Iso.refl C)

theorem below_acc (A : WellOrder.{u}) (a : A.Carrier) : Acc Below (A.below a) := by
  induction a using A.wellFounded.induction with
  | h a ih =>
    apply Acc.intro
    intro B hB
    cases hB with
    | intro b hb =>
      cases hb with
      | intro e =>
        exact acc_of_iso (e.trans (belowBelowIso A a b)) (ih b.1 b.2)

theorem below_wellFounded : WellFounded Below.{u} := by
  apply WellFounded.intro
  intro A
  apply Acc.intro
  intro B hB
  cases hB with
  | intro a ha =>
    cases ha with
    | intro e => exact acc_of_iso e (below_acc A a)

theorem Below.irrefl (A : WellOrder.{u}) : ¬ Below A A := by
  have h := below_wellFounded.apply A
  induction h with
  | intro A _ ih =>
    intro hAA
    exact ih A hAA hAA

theorem Below.trans {A B C : WellOrder.{u}} (hAB : Below A B) (hBC : Below B C) :
    Below A C := by
  cases hBC with
  | intro c hc =>
    cases hc with
    | intro e =>
      cases Below.iso_right e hAB with
      | intro b hb =>
        cases hb with
        | intro f =>
          exact Exists.intro b.1 (Nonempty.intro (f.trans (belowBelowIso C c b)))

theorem Below.congr {A B C D : WellOrder.{u}} (e : Iso A B) (f : Iso C D) :
    Below A C ↔ Below B D := by
  apply Iff.intro
  · intro h
    exact Below.iso_right f (Below.iso_left e.symm h)
  · intro h
    exact Below.iso_right f.symm (Below.iso_left e h)

theorem not_below_of_iso {A B : WellOrder.{u}} (e : Iso A B) : ¬ Below A B := by
  intro h
  exact Below.irrefl A (Below.iso_right e.symm h)

theorem below_self (A : WellOrder.{u}) (a : A.Carrier) : Below (A.below a) A :=
  Exists.intro a (Nonempty.intro (Iso.refl (A.below a)))

theorem below_below_of_lt (A : WellOrder.{u}) (a b : A.Carrier) (h : A.lt a b) :
    Below (A.below a) (A.below b) :=
  Exists.intro ⟨a, h⟩ (Nonempty.intro (belowBelowIso A b ⟨a, h⟩).symm)

theorem lt_of_below_below (A : WellOrder.{u}) (a b : A.Carrier)
    (h : Below (A.below a) (A.below b)) : A.lt a b := by
  cases A.total a b with
  | inl hab => exact hab
  | inr hrest =>
    cases hrest with
    | inl hab =>
      cases hab
      exact False.elim (Below.irrefl (A.below a) h)
    | inr hba =>
      exact False.elim
        (Below.irrefl (A.below a) (Below.trans h (below_below_of_lt A b a hba)))

theorem eq_of_below_iso (A : WellOrder.{u}) (a b : A.Carrier)
    (e : Iso (A.below a) (A.below b)) : a = b := by
  cases A.total a b with
  | inl hab => exact False.elim (not_below_of_iso e (below_below_of_lt A a b hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba =>
      exact False.elim (not_below_of_iso e.symm (below_below_of_lt A b a hba))

theorem exists_min (A : WellOrder.{u}) (P : A.Carrier → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, A.lt b a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, A.lt b c → ¬ P b := by
    intro a
    induction a using A.wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, A.lt b a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

def Matches (A B : WellOrder.{u}) (a : A.Carrier) (b : B.Carrier) : Prop :=
  Nonempty (Iso (A.below a) (B.below b))

theorem Matches.unique_left {A B : WellOrder.{u}} {a c : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c b) : a = c := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso A a c (e.trans f.symm)

theorem Matches.unique_right {A B : WellOrder.{u}} {a : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B a d) : b = d := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso B b d (e.symm.trans f)

theorem Matches.lt_iff {A B : WellOrder.{u}} {a c : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c d) : B.lt b d ↔ A.lt a c := by
  cases h with
  | intro e =>
    cases k with
    | intro f =>
      apply Iff.intro
      · intro hbd
        exact lt_of_below_below A a c
          ((Below.congr e f).mpr (below_below_of_lt B b d hbd))
      · intro hac
        exact lt_of_below_below B b d
          ((Below.congr e f).mp (below_below_of_lt A a c hac))

theorem Matches.down {A B : WellOrder.{u}} {a : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (d : B.Carrier) (hdb : B.lt d b) :
    ∃ c, A.lt c a ∧ Matches A B c d := by
  cases h with
  | intro e =>
    let c := e.invFun ⟨d, hdb⟩
    have f := ((belowBelowIso A a c).symm.trans (e.below c)).trans
      (belowBelowIso B b (e.toFun c))
    have he : (e.toFun c).1 = d := congrArg Subtype.val (e.right_inv ⟨d, hdb⟩)
    rw [he] at f
    exact Exists.intro c.1 (And.intro c.2 (Nonempty.intro f))

theorem Matches.below_right {A B : WellOrder.{u}} (b : B.Carrier)
    (a : A.Carrier) (c : (B.below b).Carrier) :
    Matches A (B.below b) a c ↔ Matches A B a c.1 := by
  apply Iff.intro
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c))
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c).symm)

theorem iso_of_matches {A B : WellOrder.{u}}
    (hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b)
    (hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b) : Nonempty (Iso A B) := by
  classical
  let f : A.Carrier → B.Carrier := fun a => Classical.choose (hA a)
  let g : B.Carrier → A.Carrier := fun b => Classical.choose (hB b)
  have hf : ∀ a, Matches A B a (f a) := fun a => Classical.choose_spec (hA a)
  have hg : ∀ b, Matches A B (g b) b := fun b => Classical.choose_spec (hB b)
  exact Nonempty.intro {
    toFun := f
    invFun := g
    left_inv := fun a => Matches.unique_left (hg (f a)) (hf a)
    right_inv := fun b => Matches.unique_right (hf (g b)) (hg b)
    lt_iff := fun a c => Matches.lt_iff (hf a) (hf c)
  }

theorem compare (A B : WellOrder.{u}) : Below A B ∨ Nonempty (Iso A B) ∨ Below B A := by
  classical
  induction A using below_wellFounded.induction generalizing B with
  | h A ih =>
    by_cases hBA : Below B A
    · exact Or.inr (Or.inr hBA)
    · have hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b := by
        intro a
        cases ih (A.below a) (below_self A a) B with
        | inl h => exact h
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro e => exact False.elim (hBA (Exists.intro a (Nonempty.intro e.symm)))
          | inr h => exact False.elim (hBA (Below.trans h (below_self A a)))
      by_cases hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b
      · exact Or.inr (Or.inl (iso_of_matches hA hB))
      · have hmissing : ∃ b : B.Carrier, ¬ ∃ a : A.Carrier, Matches A B a b :=
          Classical.not_forall.mp hB
        cases B.exists_min (fun b => ¬ ∃ a, Matches A B a b) hmissing with
        | intro b hb =>
          have hAc : ∀ a : A.Carrier, ∃ c : (B.below b).Carrier,
              Matches A (B.below b) a c := by
            intro a
            cases hA a with
            | intro c hc =>
              have hcb : B.lt c b := by
                cases B.total c b with
                | inl h => exact h
                | inr h =>
                  cases h with
                  | inl h =>
                    cases h
                    exact False.elim (hb.1 (Exists.intro a hc))
                  | inr h =>
                    cases Matches.down hc b h with
                    | intro d hd => exact False.elim (hb.1 (Exists.intro d hd.2))
              exact Exists.intro ⟨c, hcb⟩ ((Matches.below_right b a ⟨c, hcb⟩).mpr hc)
          have hBc : ∀ c : (B.below b).Carrier, ∃ a : A.Carrier,
              Matches A (B.below b) a c := by
            intro c
            have hc : ∃ a : A.Carrier, Matches A B a c.1 :=
              Classical.byContradiction (fun h => hb.2 c.1 c.2 h)
            cases hc with
            | intro a ha =>
              exact Exists.intro a ((Matches.below_right b a c).mpr ha)
          exact Or.inl (Exists.intro b (iso_of_matches hAc hBc))

end WellOrder
end OCF
