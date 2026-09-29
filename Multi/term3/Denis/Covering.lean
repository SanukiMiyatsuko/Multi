import Multi.term3.Denis.Source2019

/-! A replacement expansion with complete coverage of the represented
normal ordinals. The original C and psi definitions are unchanged.
Finite prefixes enumerate all normal terms, and each step selects the
greatest represented value below its parent in that prefix.

This module proves descent and finite-step reachability of every smaller
normal ordinal. These are not substituted for ordinal cofinality: the
latter requires a separate density theorem and treatment of uncountable
index domains.
-/

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def terms : Nat → List Term
  | 0 => [.zero]
  | n + 1 => terms n ++ (terms n).flatMap (fun a =>
      (terms n).flatMap (fun b => [.add a b, .I a b, .psi a b]))

theorem mem_terms_succ {t : Term} {n : Nat} (h : t ∈ terms n) : t ∈ terms (n + 1) :=
  List.mem_append_left _ h

theorem mem_terms_mono {t : Term} {n m : Nat} (h : n ≤ m) (ht : t ∈ terms n) :
    t ∈ terms m := by
  induction h with
  | refl => exact ht
  | step _ ih => exact mem_terms_succ ih

theorem mem_terms_binary (a b : Term) (n : Nat) (ha : a ∈ terms n) (hb : b ∈ terms n) :
    .add a b ∈ terms (n + 1) ∧ .I a b ∈ terms (n + 1) ∧ .psi a b ∈ terms (n + 1) := by
  have h (t : Term) (ht : t ∈ [.add a b, .I a b, .psi a b]) : t ∈ terms (n + 1) := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨a, ha, ?_⟩
    exact List.mem_flatMap.mpr ⟨b, hb, ht⟩
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩

theorem terms_complete (t : Term) : ∃ n, t ∈ terms n := by
  induction t with
  | zero => exact ⟨0, by simp [terms]⟩
  | add a b iha ihb | I a b iha ihb | psi a b iha ihb =>
    obtain ⟨n, hn⟩ := iha
    obtain ⟨m, hm⟩ := ihb
    have h := mem_terms_binary a b (max n m)
      (mem_terms_mono (Nat.le_max_left _ _) hn) (mem_terms_mono (Nat.le_max_right _ _) hm)
    first | exact ⟨max n m + 1, h.1⟩ | exact ⟨max n m + 1, h.2.1⟩ | exact ⟨max n m + 1, h.2.2⟩

def maxOrdinal (a b : OCF.Denis.O) : OCF.Denis.O := if a < b then b else a

theorem le_maxOrdinal_left (a b : OCF.Denis.O) : a ≤ maxOrdinal a b := by
  unfold maxOrdinal
  split
  · exact Or.inl ‹a < b›
  · exact le_refl _

theorem le_maxOrdinal_right (a b : OCF.Denis.O) : b ≤ maxOrdinal a b := by
  unfold maxOrdinal
  split
  · exact le_refl _
  · exact (not_lt_iff_le _ _).mp ‹¬ a < b›

theorem maxOrdinal_le {a b c : OCF.Denis.O} (ha : a ≤ c) (hb : b ≤ c) : maxOrdinal a b ≤ c := by
  unfold maxOrdinal
  split <;> assumption

def maximum : List OCF.Denis.O → OCF.Denis.O
  | [] => 0
  | a :: l => maxOrdinal a (maximum l)

theorem le_maximum_of_mem {a : OCF.Denis.O} {l : List OCF.Denis.O} (h : a ∈ l) : a ≤ maximum l := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_maxOrdinal_left _ _
    · exact OCF.Ordinal.le_trans (ih h) (le_maxOrdinal_right _ _)

theorem maximum_le {l : List OCF.Denis.O} {a : OCF.Denis.O}
    (h : ∀ x, x ∈ l → x ≤ a) : maximum l ≤ a := by
  induction l with
  | nil => exact zero_le _
  | cons b l ih => exact maxOrdinal_le (h b (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem maximum_lt {l : List OCF.Denis.O} {a : OCF.Denis.O}
    (ha : 0 < a) (h : ∀ x, x ∈ l → x < a) : maximum l < a := by
  induction l with
  | nil => exact ha
  | cons b l ih =>
    change maxOrdinal b (maximum l) < a
    unfold maxOrdinal
    split
    · exact ih (fun x hx => h x (by simp [hx]))
    · exact h b (by simp)

def Represented (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  ∃ t, IsNormal s t ∧ denote s t = a

theorem represented_zero (s : OCF.Denis.Supply) : Represented s 0 := ⟨.zero, .zero, rfl⟩

theorem maximum_represented (s : OCF.Denis.Supply) (l : List OCF.Denis.O)
    (h : ∀ x, x ∈ l → Represented s x) : Represented s (maximum l) := by
  induction l with
  | nil => exact represented_zero s
  | cons b l ih =>
    change Represented s (maxOrdinal b (maximum l))
    unfold maxOrdinal
    split
    · exact ih (fun x hx => h x (by simp [hx]))
    · exact h b (by simp)

def candidate (s : OCF.Denis.Supply) (a : OCF.Denis.O) (t : Term) : OCF.Denis.O :=
  if IsNormal s t ∧ denote s t < a then denote s t else 0

theorem candidate_represented (s : OCF.Denis.Supply) (a : OCF.Denis.O) (t : Term) :
    Represented s (candidate s a t) := by
  unfold candidate
  split
  · exact ⟨t, ‹IsNormal s t ∧ denote s t < a›.1, rfl⟩
  · exact represented_zero s

theorem candidate_lt (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : 0 < a) (t : Term) :
    candidate s a t < a := by
  unfold candidate
  split
  · exact ‹IsNormal s t ∧ denote s t < a›.2
  · exact ha

def value (s : OCF.Denis.Supply) (a : OCF.Denis.O) (n : Nat) : OCF.Denis.O :=
  maximum ((terms n).map (candidate s a))

theorem value_represented (s : OCF.Denis.Supply) (a : OCF.Denis.O) (n : Nat) :
    Represented s (value s a n) := by
  apply maximum_represented
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact candidate_represented s a t

theorem value_lt (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : 0 < a) (n : Nat) :
    value s a n < a := by
  apply maximum_lt ha
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact candidate_lt s a ha t

theorem value_mono (s : OCF.Denis.Supply) (a : OCF.Denis.O) {n m : Nat} (h : n ≤ m) :
    value s a n ≤ value s a m := by
  apply maximum_le
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact le_maximum_of_mem (List.mem_map.mpr ⟨t, mem_terms_mono h ht, rfl⟩)

/-- Every smaller normal value is eventually dominated by the expansion. -/
theorem value_covers (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (hb : Represented s b) (hba : b < a) : ∃ n, b ≤ value s a n := by
  obtain ⟨t, ht, rfl⟩ := hb
  obtain ⟨n, hn⟩ := terms_complete t
  refine ⟨n, ?_⟩
  have h := le_maximum_of_mem (List.mem_map.mpr ⟨t, hn, rfl⟩ :
    candidate s a t ∈ (terms n).map (candidate s a))
  rwa [candidate, ite_eq_left ⟨ht, hba⟩] at h

def step (s : OCF.Denis.Supply) (a : NormalOrdinal s) (n : Nat) : NormalOrdinal s :=
  ⟨value s a.1 n, value_represented s a.1 n⟩

inductive Reachable (s : OCF.Denis.Supply) : NormalOrdinal s → NormalOrdinal s → Prop where
  | refl (a) : Reachable s a a
  | step (a b : NormalOrdinal s) (n : Nat) : Reachable s b (step s a n) → Reachable s b a

/-- Complete finite-step coverage, not just a few computed examples. -/
theorem reachable_of_lt (s : OCF.Denis.Supply) (a b : NormalOrdinal s) (hba : b.1 < a.1) :
    Reachable s b a := by
  induction a using (normalOrdinalWellOrder s).wellFounded.induction with
  | h a ih =>
    obtain ⟨n, hn⟩ := value_covers s a.1 b.1 b.2 hba
    have ha : 0 < a.1 := OCF.Ordinal.lt_of_le_of_lt (zero_le b.1) hba
    rcases hn with h | h
    · exact .step a b n (ih (step s a n) (value_lt s a.1 ha n) h)
    · have heq : b = step s a n := Subtype.ext h
      exact .step a b n (heq ▸ Reachable.refl b)

/-- The additional condition needed to infer cofinality in actual ordinals. -/
def DenseBelow (s : OCF.Denis.Supply) (a : OCF.Denis.O) : Prop :=
  ∀ x, x < a → ∃ b, Represented s b ∧ x < b ∧ b < a

theorem value_cofinal_of_dense (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (h : DenseBelow s a) : ∀ x, x < a → ∃ n, x < value s a n := by
  intro x hx
  obtain ⟨b, hb, hxb, hba⟩ := h x hx
  obtain ⟨n, hn⟩ := value_covers s a b hb hba
  exact ⟨n, OCF.Ordinal.lt_of_lt_of_le hxb hn⟩

end
end T.Correspondence.Denis.Covering
