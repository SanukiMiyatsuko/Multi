import Multi.term3.Term3Normal

/-!
Concrete comparisons with Denis Maksudov's December 2019 notation and
fundamental-sequence rules (Section 2, clauses 10.2, 10.6, 10.7, 10.14, 10.15):
https://sites.google.com/site/travelingtotheinfinity/the-collapsing-functions-using-math-alpha-beta-math--weakly-inaccessible-cardinals

`Denis.Term` is a syntax, NOT a quotient of actual ordinals. In particular,
the comparisons below do not assume an ordinal interpretation or the
unproved well-foundedness statements in Term3.lean. Names of ordinal
notations must not be confused with proved equalities of ordinal values.
-/

namespace T.Correspondence

open T

def one : T := P Z Z Z Z
def exp (a : T) : T := P Z Z a Z
def card (a : T) : T := P Z a Z Z
def uncountable : T := card one
def inaccessible : T := P one Z Z Z
def epsilon : T := exp uncountable
def collapseI : T := exp inaccessible
def cardFixed : T := card inaccessible

def iterate (f : T → T) : Nat → T
  | 0 => Z
  | n + 1 => f (iterate f n)

theorem iter_ofNat (f : T → T) (n : Nat) :
    T.iter f (T.ofNat n) = iterate f n := by
  induction n with
  | zero => rfl
  | succ n ih => change f (T.iter f (T.ofNat n)) = f (iterate f n); rw [ih]

theorem fund_one (t : T) : T.fund one t = Z := by
  rw [one, T.fund]; rfl

theorem ofNat_add_one (n : Nat) : T.ofNat n + one = T.ofNat (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P Z Z Z (T.ofNat n + one) = P Z Z Z (T.ofNat (n + 1))
    rw [ih]

theorem mul_one_ofNat (n : Nat) : T.mul one (T.ofNat n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.mul one (T.ofNat n) + one = T.ofNat (n + 1)
    rw [ih, ofNat_add_one]

theorem fund_omega (n : Nat) : T.fund (exp one) (T.ofNat n) = T.ofNat n := by
  unfold exp
  rw [T.fund, ite_eq_left rfl]
  change T.mul (P Z Z (T.fund one Z) Z) (T.ofNat n) = _
  rw [fund_one]
  exact mul_one_ofNat n

theorem fund_ofNat_succ (n : Nat) (t : T) : T.fund (T.ofNat (n + 1)) t = T.ofNat n := by
  induction n with
  | zero => exact fund_one t
  | succ n ih =>
    change T.fund (P Z Z Z (T.ofNat (n + 1))) t = _
    rw [T.fund, ite_eq_right (show T.ofNat (n + 1) ≠ Z from T.noConfusion)]
    change P Z Z Z (T.fund (T.ofNat (n + 1)) t) = P Z Z Z (T.ofNat n)
    rw [ih]

theorem fund_uncountable (t : T) : T.fund uncountable t = t := by
  rw [uncountable, card, T.fund]; rfl

theorem fund_inaccessible (t : T) : T.fund inaccessible t = t := by
  rw [inaccessible, T.fund]; rfl

theorem dom_uncountable : T.dom uncountable = .Ω Z one := rfl
theorem dom_inaccessible : T.dom inaccessible = .Ω one Z := rfl

theorem exp_lt_uncountable (a : T) : exp a < uncountable :=
  T.lt.p_second _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)

theorem exp_lt_inaccessible (a : T) : exp a < inaccessible :=
  T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)

theorem card_lt_inaccessible (a : T) : card a < inaccessible :=
  T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)

theorem fund_epsilon (n : Nat) :
    T.fund epsilon (T.ofNat n) = iterate exp (n + 1) := by
  unfold epsilon exp
  rw [T.fund, ite_eq_left rfl, dom_uncountable]
  simp only [show P Z Z uncountable Z < P Z one Z Z from exp_lt_uncountable uncountable,
    ↓reduceIte]
  change P Z Z (T.fund uncountable
    (T.iter (fun x => P Z (T.fund one Z) (T.fund uncountable x) Z) (T.ofNat n))) Z = _
  simp only [fund_one, fund_uncountable]
  exact congrArg exp (iter_ofNat exp n)

theorem fund_cardFixed (n : Nat) :
    T.fund cardFixed (T.ofNat n) = iterate card (n + 1) := by
  unfold cardFixed card
  rw [T.fund, ite_eq_left rfl]
  change (if P Z inaccessible Z Z < inaccessible then
    P Z (T.fund inaccessible
      (T.iter (fun x => P (T.fund one Z) (T.fund inaccessible x) Z Z) (T.ofNat n))) Z Z
    else P Z (T.fund inaccessible (T.ofNat n)) Z Z) = _
  simp only [show P Z inaccessible Z Z < inaccessible from card_lt_inaccessible inaccessible,
    ↓reduceIte]
  simp only [fund_one, fund_inaccessible]
  exact congrArg card (iter_ofNat card n)

theorem fund_collapseI (n : Nat) :
    T.fund collapseI (T.ofNat n) = exp (iterate card n) := by
  unfold collapseI exp
  rw [T.fund, ite_eq_left rfl, dom_inaccessible]
  simp only [show P Z Z inaccessible Z < P one Z Z Z from exp_lt_inaccessible inaccessible,
    ↓reduceIte]
  change P Z Z (T.fund inaccessible
    (T.iter (fun x => P (T.fund one Z) (T.fund inaccessible x) Z Z) (T.ofNat n))) Z = _
  simp only [fund_one, fund_inaccessible]
  exact congrArg exp (iter_ofNat card n)

theorem dom_epsilon : T.dom epsilon = .ω := by
  unfold epsilon exp
  rw [T.dom, ite_eq_left rfl, dom_uncountable]
  exact ite_eq_left (exp_lt_uncountable uncountable)

theorem dom_collapseI : T.dom collapseI = .ω := by
  unfold collapseI exp
  rw [T.dom, ite_eq_left rfl, dom_inaccessible]
  exact ite_eq_left (exp_lt_inaccessible inaccessible)

theorem dom_cardFixed : T.dom cardFixed = .ω := by
  unfold cardFixed card
  rw [T.dom, ite_eq_left rfl]
  exact ite_eq_left (card_lt_inaccessible inaccessible)

theorem one_isOT : T.isOT one := T.isOT.base 0
theorem omega_isOT : T.isOT (exp one) := T.isOT.base 1
theorem collapseI_isOT : T.isOT collapseI := T.isOT.base 2

theorem ofNat_isOT (n : Nat) : T.isOT (T.ofNat n) := by
  rw [← fund_omega]
  exact T.isOT.step (exp one) omega_isOT n

theorem epsilon_isOT : T.isOT epsilon := by
  have h := T.isOT.step collapseI collapseI_isOT 2
  rw [fund_collapseI] at h
  exact h

theorem exp_tower_isOT (n : Nat) : T.isOT (iterate exp n) := by
  cases n with
  | zero =>
    have h := T.isOT.step one one_isOT 0
    rw [fund_one] at h
    exact h
  | succ n => rw [← fund_epsilon]; exact T.isOT.step epsilon epsilon_isOT n

theorem collapseI_child_isOT (n : Nat) : T.isOT (exp (iterate card n)) := by
  rw [← fund_collapseI]
  exact T.isOT.step collapseI collapseI_isOT n

theorem uncountable_not_isOT : ¬ T.isOT uncountable := by
  intro h
  exact T.lt_irrefl uncountable (T.OT_lt_first_uncountable _ h)

theorem inaccessible_not_isOT : ¬ T.isOT inaccessible := by
  intro h
  exact T.lt_asymm (card_lt_inaccessible one) (T.OT_lt_first_uncountable _ h)

theorem cardFixed_not_isOT : ¬ T.isOT cardFixed := by
  intro h
  have hi : one < inaccessible := T.lt.p_first _ _ _ _ _ _ _ _ (T.lt.Z_lt_P _ _ _ _)
  have ho : uncountable < cardFixed := T.lt.p_second _ _ _ _ _ _ _ hi
  exact T.lt_asymm ho (T.OT_lt_first_uncountable _ h)

namespace Denis

/-- Raw syntax of the cited notation, with binary sums. -/
inductive Term where
  | zero
  | add (a b : Term)
  | I (a b : Term)
  | psi (k a : Term)
  deriving DecidableEq, Repr

def omega1 : Term := .I .zero .zero
def I1 : Term := .I (.psi omega1 .zero) .zero
def one : Term := .psi omega1 .zero
def exp (a : Term) : Term := .psi omega1 a
def epsilon : Term := .psi omega1 omega1
def collapseI : Term := .psi omega1 I1
def cardFixed : Term := .psi I1 .zero

def iterate (f : Term → Term) (z : Term) : Nat → Term
  | 0 => z
  | n + 1 => f (iterate f z n)

/-- Clause 10.15 at psi_{I(0,0)}(I(0,0)), using 10.3. -/
def epsilonSeq (n : Nat) : Term := exp (iterate exp one n)

/-- Clause 10.7 at psi_{I(1,0)}(0). -/
def cardFixedSeq (n : Nat) : Term := iterate (.I .zero) .zero n

/-- Clause 10.15 at psi_{I(0,0)}(I(1,0)), using 10.3. -/
def collapseISeq (n : Nat) : Term :=
  exp (iterate (.psi I1) one n)

theorem epsilonSeq_zero : epsilonSeq 0 = exp one := rfl
theorem collapseISeq_zero : collapseISeq 0 = exp one := rfl
theorem cardFixedSeq_zero : cardFixedSeq 0 = .zero := rfl

end Denis

/-- The direct structural reading on the explicitly supported fragment.
Unsupported heads return `none`; no ordinal value is fabricated for them. -/
def direct : T → Option Denis.Term
  | Z => some .zero
  | P a b c d => do
    let head ←
      if a = Z ∧ b = Z then
        (direct c).map Denis.exp
      else if a = Z ∧ b = one ∧ c = Z then
        some Denis.omega1
      else if a = one ∧ b = Z ∧ c = Z then
        some Denis.I1
      else none
    if d = Z then some head
    else (direct d).map (.add head)

theorem direct_zero : direct Z = some .zero := rfl
theorem direct_exp (a : T) : direct (exp a) = (direct a).map Denis.exp := by
  simp only [exp, direct, and_self, ↓reduceIte]
  cases direct a <;> rfl

theorem direct_one : direct one = some Denis.one := rfl
theorem direct_one_tail (t : T) (ht : t ≠ Z) :
    direct (P Z Z Z t) = (direct t).map (Denis.Term.add Denis.one) := by
  rw [direct]
  simp only [and_self, ↓reduceIte]
  simp only [direct_zero]
  change (if t = Z then some Denis.one else
    (direct t).map (Denis.Term.add Denis.one)) = _
  rw [ite_eq_right ht]

theorem direct_uncountable : direct uncountable = some Denis.omega1 := rfl
theorem direct_inaccessible : direct inaccessible = some Denis.I1 := rfl
theorem direct_epsilon : direct epsilon = some Denis.epsilon := by
  rw [epsilon, direct_exp, direct_uncountable]; rfl
theorem direct_collapseI : direct collapseI = some Denis.collapseI := by
  rw [collapseI, direct_exp, direct_inaccessible]; rfl

theorem direct_exp_tower (n : Nat) :
    direct (iterate exp n) = some (Denis.iterate Denis.exp .zero n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, direct_exp, ih]; rfl

theorem denis_exp_tower_shift (n : Nat) :
    Denis.iterate Denis.exp .zero (n + 1) = Denis.iterate Denis.exp Denis.one n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Denis.exp ih

/-- The two epsilon fundamental sequences agree after a shift by one. -/
theorem epsilon_sequence_shift (n : Nat) :
    direct (T.fund epsilon (T.ofNat (n + 1))) = some (Denis.epsilonSeq n) := by
  rw [fund_epsilon, direct_exp_tower]
  exact congrArg (fun t => some (Denis.exp t)) (denis_exp_tower_shift n)

/-- Even at epsilon, the unshifted sequences are not identical. -/
theorem epsilon_sequence_zero_ne :
    direct (T.fund epsilon (T.ofNat 0)) ≠ some (Denis.epsilonSeq 0) := by
  rw [fund_epsilon, direct_exp_tower]
  decide

/-- The direct reading of the first inaccessible collapse also fails at 0. -/
theorem collapseI_sequence_zero_ne :
    direct (T.fund collapseI (T.ofNat 0)) ≠ some (Denis.collapseISeq 0) := by
  rw [fund_collapseI]
  change some Denis.one ≠ some (Denis.exp Denis.one)
  decide

/-- The epsilon shift does not repair the next branch: Term3 gives epsilon,
whereas Denis gives psi_{omega1}(psi_{I1}(1)). This is syntactic inequality. -/
theorem collapseI_sequence_shift_one_ne :
    direct (T.fund collapseI (T.ofNat (1 + 1))) ≠ some (Denis.collapseISeq 1) := by
  rw [fund_collapseI]
  change direct epsilon ≠ _
  rw [direct_epsilon]
  decide

end T.Correspondence
