import Multi.term3.Denis.SequenceObstruction

/-! Direct checks of the 2019 source's syntactic rules.
Binary sums below represent right-associated lists of principal summands.
Comparisons are used on admissible inputs; the fallback for malformed
collapse indices does not participate in any theorem here.

Source: Section 2, clauses 6--10 of
https://sites.google.com/site/travelingtotheinfinity/the-collapsing-functions-using-math-alpha-beta-math--weakly-inaccessible-cardinals
-/

namespace T.Correspondence.Denis.Source2019

def lt : Term → Term → Bool
  | .zero, .zero => false
  | .zero, _ => true
  | _, .zero => false
  | .add a b, .add c d => if a = c then lt b d else lt a c
  | .add a _, b => lt a b
  | a, .add b _ => a == b || lt a b
  | x@(.I a b), y@(.I c d) =>
    (lt a c && lt b y) || (a == c && lt b d) || (lt c a && lt x d)
  | x@(.I b c), y@(.psi k@(.I r _) _) =>
    (lt b r && lt c y) || ((r == b || lt r b) && lt x k)
  | x@(.psi k@(.I r _) _), y@(.I b c) =>
    !((lt b r && lt c x) || ((r == b || lt r b) && lt y k))
  | x@(.psi k a), y@(.psi p b) =>
    (lt k p && lt k y) || (k == p && lt a b) || (lt p k && lt x p)
  | _, _ => false
termination_by a b => sizeOf a + sizeOf b

def le (a b : Term) : Bool := a == b || lt a b

def e : Term → Term
  | .zero | .add _ _ => .zero
  | .I r _ => r
  | .psi k _ => e k

def G (k : Term) : Term → List Term
  | .zero => []
  | .add a b | .I a b => G k a ++ G k b
  | .psi p b => if lt p k then [] else b :: (G k p ++ G k b)

def successor : Term → Bool
  | t@(.psi _ _) => t == one
  | .add _ b => successor b
  | _ => false

def regular : Term → Bool
  | .I _ b => b == .zero || successor b
  | _ => false

/-- Clauses 6.1--6.7, combining the successor/limit cases of sums and I.
The sum representation is binary and right-associated. -/
inductive OT : Term → Prop where
  | zero : OT .zero
  | one : OT one
  | sum {a b : Term} : OT a → OT b → a.isPrincipal → b ≠ .zero →
      le b.leading a = true → lt a (.add a b) = true → OT (.add a b)
  | index {r b : Term} : OT r → OT b → le (e b) r = true → OT (.I r b)
  | collapse {k a : Term} : OT k → OT a → regular k = true →
      (∀ x, x ∈ G k a → lt x a = true) → lt one (.psi k a) = true → OT (.psi k a)

def pred : Term → Term
  | .psi _ _ => .zero
  | .add a b => match pred b with
    | .zero => a
    | c => .add a c
  | _ => .zero

/-- The source's star operation following rule 10.15. -/
def star : Term → Term
  | .I r b => if le (e (pred b)) r then .I r (pred b) else pred b
  | _ => .zero

def repeatTerm (a : Term) : Nat → Term
  | 0 => .zero
  | 1 => a
  | n + 2 => .add a (repeatTerm a (n + 1))

/-- Rule 10.5, including its star normalisation and the tensor operation. -/
def ruleFive (index : Term) (n : Nat) : Term := repeatTerm (star index) n

theorem omega1_OT : OT omega1 := .index .zero .zero (by decide)
theorem I1_OT : OT I1 := .index .one .zero (by simp [le, e, lt, omega1])

theorem cardFixed_OT : OT cardFixed := by
  apply OT.collapse I1_OT .zero (by decide)
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · simp [lt, one, I1, omega1]

theorem obstructionIndexTerm_OT : OT obstructionIndexTerm := by
  apply OT.index .zero
  · apply OT.sum cardFixed_OT .one (by trivial) (by decide)
    · simp [le, Term.leading, lt, one, cardFixed, I1, omega1]
    · simp [lt, cardFixed]
  · simp [le, e]

theorem obstructionTerm_OT : OT obstructionTerm := by
  apply OT.collapse obstructionIndexTerm_OT .zero (by decide)
  · intro x hx
    exact False.elim (List.not_mem_nil hx)
  · simp [lt, obstructionIndexTerm, cardFixed, one, I1, omega1]

theorem obstructionIndex_successor : successor (.add cardFixed one) = true := by decide

theorem obstruction_star : star obstructionIndexTerm = cardFixed := by
  simp [star, obstructionIndexTerm, pred, le, e, lt, one, I1, omega1, cardFixed]

theorem obstruction_ruleFive_one : ruleFive obstructionIndexTerm 1 = cardFixed := by
  rw [ruleFive, repeatTerm, obstruction_star]

theorem obstruction_source_strict : lt cardFixed obstructionTerm = true := by
  simp [obstructionTerm, obstructionIndexTerm, lt, one, I1, omega1, cardFixed]

/-- Rule 10.5 produces a non-descending element at an OT term. -/
theorem ruleFive_counterexample (s : OCF.Denis.Supply) :
    OT obstructionTerm ∧
    ¬ denote s (ruleFive obstructionIndexTerm 1) < denote s obstructionTerm := by
  refine ⟨obstructionTerm_OT, ?_⟩
  rw [obstruction_ruleFive_one, denote_cardFixed, denote_obstructionTerm]
  exact OCF.Denis.obstruction_base_not_below s

/-- Clause 9's syntactic comparison disagrees with the closure semantics. -/
theorem order_semantics_counterexample (s : OCF.Denis.Supply) :
    OT cardFixed ∧ OT obstructionTerm ∧ lt cardFixed obstructionTerm = true ∧
      ¬ denote s cardFixed < denote s obstructionTerm := by
  refine ⟨cardFixed_OT, obstructionTerm_OT, obstruction_source_strict, ?_⟩
  rw [denote_cardFixed, denote_obstructionTerm]
  exact OCF.Denis.obstruction_base_not_below s

theorem ruleFive_first_equals_parent (s : OCF.Denis.Supply) :
    denote s (ruleFive obstructionIndexTerm 1) = denote s obstructionTerm := by
  rw [obstruction_ruleFive_one, denote_cardFixed, denote_obstructionTerm,
    OCF.Denis.obstructionValue_eq_base]

theorem ruleFive_not_fundamentalSequence (s : OCF.Denis.Supply) :
    ¬ OCF.Denis.FundamentalSequence (denote s obstructionTerm)
      (fun n => denote s (ruleFive obstructionIndexTerm n)) := by
  intro h
  have hh := h.below 1
  rw [ruleFive_first_equals_parent] at hh
  exact OCF.Ordinal.lt_irrefl _ hh

end T.Correspondence.Denis.Source2019
