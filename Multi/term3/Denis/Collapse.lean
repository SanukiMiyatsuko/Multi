import Multi.term3.Denis.Cardinals

/-!
Denis's closure on actual ordinals: start with beta and 0, close under
ordinal addition, I, and earlier collapses at regular indices.

The recursive construction includes kappa as a boundary value. The module
`WellDefined` proves that the value is strictly below every regular index,
and satisfies the unique minimum specification in the published definition.
Strict existence is proved from regularity, not assumed as a structure field.
-/

namespace OCF.Denis

open Ordinal

noncomputable section

structure Stage where
  closed : O → O → Prop
  collapse : O → O

inductive StageClosure (s : Supply) (a : O)
    (previous : (b : O) → b < a → Stage) (beta : O) : O → Prop where
  | zero : StageClosure s a previous beta 0
  | seed {x : O} : x < beta → StageClosure s a previous beta x
  | add {x y : O} : StageClosure s a previous beta x →
      StageClosure s a previous beta y → StageClosure s a previous beta (x + y)
  | index {x y : O} : StageClosure s a previous beta x →
      StageClosure s a previous beta y → StageClosure s a previous beta (I s x y)
  | collapse {k b : O} (hb : b < a) : RegularIndex s k →
      StageClosure s a previous beta k → StageClosure s a previous beta b →
      StageClosure s a previous beta ((previous b hb).collapse k)

def ClosedBelow (closed : O → O → Prop) (k beta : O) : Prop :=
  beta ≤ k ∧ ∀ x, closed beta x → x < k → x < beta

theorem closedBelow_self (closed : O → O → Prop) (k : O) :
    ClosedBelow closed k k := ⟨le_refl k, fun _ _ hx => hx⟩

def makeStage (s : Supply) (a : O) (previous : (b : O) → b < a → Stage) : Stage where
  closed := StageClosure s a previous
  collapse k := least (ClosedBelow (StageClosure s a previous) k)
    ⟨k, closedBelow_self _ k⟩

def stages (s : Supply) : O → Stage :=
  lt_wellFounded.fix (fun a previous => makeStage s a previous)

theorem stages_eq (s : Supply) (a : O) :
    stages s a = makeStage s a (fun b _ => stages s b) :=
  WellFounded.fix_eq lt_wellFounded _ a

def C (s : Supply) (a beta x : O) : Prop := (stages s a).closed beta x
def psi (s : Supply) (k a : O) : O := (stages s a).collapse k

theorem C_iff (s : Supply) (a beta x : O) :
    C s a beta x ↔ StageClosure s a (fun b _ => stages s b) beta x := by
  unfold C
  rw [stages_eq]
  rfl

theorem C_zero (s : Supply) (a beta : O) : C s a beta 0 :=
  (C_iff s a beta 0).mpr .zero

theorem C_seed (s : Supply) (a beta x : O) (hx : x < beta) : C s a beta x :=
  (C_iff s a beta x).mpr (.seed hx)

theorem C_add (s : Supply) (a beta x y : O)
    (hx : C s a beta x) (hy : C s a beta y) : C s a beta (x + y) :=
  (C_iff s a beta _).mpr (.add ((C_iff s a beta x).mp hx) ((C_iff s a beta y).mp hy))

theorem C_index (s : Supply) (a beta x y : O)
    (hx : C s a beta x) (hy : C s a beta y) : C s a beta (I s x y) :=
  (C_iff s a beta _).mpr (.index ((C_iff s a beta x).mp hx) ((C_iff s a beta y).mp hy))

theorem C_collapse (s : Supply) (a beta k b : O) (hb : b < a)
    (hk : RegularIndex s k) (hc : C s a beta k) (hd : C s a beta b) :
    C s a beta (psi s k b) :=
  (C_iff s a beta _).mpr
    (.collapse hb hk ((C_iff s a beta k).mp hc) ((C_iff s a beta b).mp hd))

/-- Universal property: C is the least set with the four required closures. -/
theorem C_least (s : Supply) (a beta : O) (P : O → Prop)
    (hz : P 0) (hseed : ∀ x, x < beta → P x)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hindex : ∀ x y, P x → P y → P (I s x y))
    (hpsi : ∀ k b, b < a → RegularIndex s k → P k → P b → P (psi s k b))
    (x : O) (hx : C s a beta x) : P x := by
  have h := (C_iff s a beta x).mp hx
  clear hx
  induction h with
  | zero => exact hz
  | seed hx => exact hseed _ hx
  | add _ _ ihx ihy => exact hadd _ _ ihx ihy
  | index _ _ ihx ihy => exact hindex _ _ ihx ihy
  | collapse hb hk _ _ ihk ihb => exact hpsi _ _ hb hk ihk ihb

theorem C_mono_seed (s : Supply) (a beta gamma : O) (hbg : beta ≤ gamma)
    (x : O) (hx : C s a beta x) : C s a gamma x := by
  apply C_least s a beta (C s a gamma) (C_zero s a gamma) _ _ _ _ x hx
  · exact fun x hx => C_seed s a gamma x (lt_of_lt_of_le hx hbg)
  · exact C_add s a gamma
  · exact C_index s a gamma
  · exact C_collapse s a gamma

theorem C_mono_argument (s : Supply) (a b beta : O) (hab : a ≤ b)
    (x : O) (hx : C s a beta x) : C s b beta x := by
  apply C_least s a beta (C s b beta) (C_zero s b beta) _ _ _ _ x hx
  · exact C_seed s b beta
  · exact C_add s b beta
  · exact C_index s b beta
  · intro k c hc hk hck hcc
    exact C_collapse s b beta k c (lt_of_lt_of_le hc hab) hk hck hcc

theorem psi_closedBelow (s : Supply) (k a : O) :
    ClosedBelow (C s a) k (psi s k a) := by
  unfold C psi
  rw [stages_eq]
  exact (least_spec (ClosedBelow (StageClosure s a (fun b _ => stages s b)) k)
    ⟨k, closedBelow_self _ k⟩).1

theorem psi_le (s : Supply) (k a : O) : psi s k a ≤ k :=
  (psi_closedBelow s k a).1

theorem psi_closed (s : Supply) (k a x : O)
    (hx : C s a (psi s k a) x) (hk : x < k) : x < psi s k a :=
  (psi_closedBelow s k a).2 x hx hk

theorem psi_min (s : Supply) (k a beta : O)
    (h : ClosedBelow (C s a) k beta) : psi s k a ≤ beta := by
  unfold C psi at *
  rw [stages_eq] at *
  exact least_le (ClosedBelow (StageClosure s a (fun b _ => stages s b)) k)
    ⟨k, closedBelow_self _ k⟩ h

theorem psi_mono (s : Supply) (k a b : O) (hab : a ≤ b) :
    psi s k a ≤ psi s k b := by
  apply psi_min
  exact ⟨psi_le s k b, fun x hx hk =>
    psi_closed s k b x (C_mono_argument s a b _ hab x hx) hk⟩

/-- Exact criterion for the strict minimum in Denis's definition. -/
theorem psi_lt_iff (s : Supply) (k a : O) :
    psi s k a < k ↔ ∃ beta, beta < k ∧
      ∀ x, C s a beta x → x < k → x < beta := by
  constructor
  · intro h
    exact ⟨psi s k a, h, (psi_closedBelow s k a).2⟩
  · rintro ⟨beta, hb, hc⟩
    exact lt_of_le_of_lt (psi_min s k a beta ⟨Or.inl hb, hc⟩) hb

theorem psi_pos (s : Supply) (k a : O) (hk : 0 < k) : 0 < psi s k a :=
  psi_closed s k a 0 (C_zero s a _) hk

/-- Any ordinal satisfying the published minimum specification is our value. -/
theorem psi_eq_of_spec (s : Supply) (k a beta : O) (hb : beta < k)
    (hc : ∀ x, C s a beta x → x < k → x < beta)
    (hmin : ∀ gamma, gamma < k →
      (∀ x, C s a gamma x → x < k → x < gamma) → beta ≤ gamma) :
    psi s k a = beta := by
  have hle := psi_min s k a beta ⟨Or.inl hb, hc⟩
  exact le_antisymm hle (hmin _ (lt_of_le_of_lt hle hb) (psi_closedBelow s k a).2)

theorem I_lower_bound (s : Supply) (a b : O) : I s 0 0 ≤ I s a b := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    classical
    rw [I_eq s a b]
    split
    · rw [I_zero]
      exact first_le s 0 _ ((inaccessible_zero_iff _).mpr
        (inaccessible_regular (first_spec s a)))
    · split
      · rename_i hb
        rw [I_zero]
        exact first_le s 0 _ ((inaccessible_zero_iff _).mpr
          (inaccessible_regular (next_spec s a _).2))
      · rename_i hzero hsucc
        have hz : 0 < b := (zero_lt_iff_ne_zero b).mpr hzero
        obtain ⟨x, hx⟩ := initial_surjective b 0 hz
        have h := le_sup (fun x : (representative b).Carrier =>
          I s a (type ((representative b).below x))) x
        rw [← hx] at h
        exact le_trans (ih 0 hz) h

theorem C_zero_below_first (s : Supply) (x : O)
    (hx : C s 0 (succ 0) x) (hbound : x < I s 0 0) : x = 0 := by
  have h := (C_iff s 0 (succ 0) x).mp hx
  clear hx
  induction h with
  | zero => rfl
  | seed hx =>
    exact le_antisymm ((lt_succ_iff_le _ _).mp hx) (zero_le _)
  | @add x y hx hy ihx ihy =>
    have hx0 := ihx (lt_of_le_of_lt (le_add x y) hbound)
    have hy0 := ihy (lt_of_le_of_lt (right_le_add x y) hbound)
    rw [hx0, hy0, add_zero]
  | @index x y hx hy ihx ihy =>
    exact False.elim (((not_lt_iff_le _ _).mpr (I_lower_bound s x y)) hbound)
  | collapse hb _ _ _ _ _ => exact False.elim (not_lt_zero _ hb)

/-- An actual ordinal equality, proved from the closure definition. -/
theorem psi_first_zero (s : Supply) : psi s (I s 0 0) 0 = succ 0 := by
  have hreg := regularIndex_regular s (I s 0 0) (Or.inl ⟨0, rfl⟩)
  have homega : 0 ≤ omega := zero_le _
  have hk : 0 < I s 0 0 := lt_of_le_of_lt homega hreg.1
  apply le_antisymm
  · apply psi_min
    refine ⟨(succ_le_iff_lt _ _).mpr hk, ?_⟩
    intro x hx hbound
    rw [C_zero_below_first s x hx hbound]
    exact lt_succ_self 0
  · exact (succ_le_iff_lt _ _).mpr (psi_pos s _ _ hk)

theorem regularIndex_lower_bound (s : Supply) (k : O) (hk : RegularIndex s k) :
    I s 0 0 ≤ k := by
  rcases hk with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> exact I_lower_bound s _ _

theorem psi_zero_below_first (s : Supply) (k : O) (hk : RegularIndex s k)
    (hbound : psi s k 0 < I s 0 0) : psi s k 0 = succ 0 := by
  cases regularIndex_lower_bound s k hk with
  | inr heq => rw [← heq]; exact psi_first_zero s
  | inl hlt =>
    have hmem : C s 0 (psi s k 0) (I s 0 0) :=
      C_index s 0 _ 0 0 (C_zero s 0 _) (C_zero s 0 _)
    exact False.elim (lt_asymm hbound (psi_closed s k 0 _ hmem hlt))

theorem C_one_below_first (s : Supply) (x : O)
    (hx : C s (succ 0) omega x) (hbound : x < I s 0 0) : x < omega := by
  have h := (C_iff s (succ 0) omega x).mp hx
  clear hx
  induction h with
  | zero => exact finite_lt_omega 0
  | seed hx => exact hx
  | @add x y hx hy ihx ihy =>
    exact omega_add_closed (ihx (lt_of_le_of_lt (le_add x y) hbound))
      (ihy (lt_of_le_of_lt (right_le_add x y) hbound))
  | @index x y hx hy ihx ihy =>
    exact False.elim (((not_lt_iff_le _ _).mpr (I_lower_bound s x y)) hbound)
  | @collapse k b hb hk hc hd ihc ihd =>
    have hb0 : b = 0 := le_antisymm ((lt_succ_iff_le b 0).mp hb) (zero_le b)
    cases hb0
    change psi s k 0 < omega
    rw [psi_zero_below_first s k hk hbound]
    exact finite_lt_omega 1

/-- Another equality of actual ordinals, not an equation between syntax trees. -/
theorem psi_first_one (s : Supply) : psi s (I s 0 0) (succ 0) = omega := by
  have hreg := regularIndex_regular s (I s 0 0) (Or.inl ⟨0, rfl⟩)
  have hupper : psi s (I s 0 0) (succ 0) ≤ omega :=
    psi_min s _ _ omega ⟨Or.inl hreg.1, fun x hx hbound => C_one_below_first s x hx hbound⟩
  have hfinite : ∀ n, C s (succ 0) (psi s (I s 0 0) (succ 0)) (finite n) := by
    intro n
    induction n with
    | zero => exact C_zero s _ _
    | succ n ih =>
      have hI := C_index s (succ 0) (psi s (I s 0 0) (succ 0)) 0 0
        (C_zero s _ _) (C_zero s _ _)
      have hone := C_collapse s (succ 0) (psi s (I s 0 0) (succ 0))
        (I s 0 0) 0 (lt_succ_self 0) (Or.inl ⟨0, rfl⟩) hI (C_zero s _ _)
      rw [psi_first_zero] at hone
      have h := C_add s (succ 0) (psi s (I s 0 0) (succ 0)) _ _ ih hone
      rw [add_succ, add_zero] at h
      exact h
  apply le_antisymm hupper
  apply (sup_le_iff finite _).mpr
  intro n
  exact Or.inl (psi_closed s _ _ (finite n) (hfinite n)
    (lt_trans _ _ _ (finite_lt_omega n) hreg.1))

theorem psi_first_zero_strict (s : Supply) : psi s (I s 0 0) 0 < I s 0 0 := by
  rw [psi_first_zero]
  exact lt_trans _ _ _ (finite_lt_omega 1)
    (regularIndex_regular s _ (Or.inl ⟨0, rfl⟩)).1

theorem psi_first_one_strict (s : Supply) : psi s (I s 0 0) (succ 0) < I s 0 0 := by
  rw [psi_first_one]
  exact (regularIndex_regular s _ (Or.inl ⟨0, rfl⟩)).1

end
end OCF.Denis
