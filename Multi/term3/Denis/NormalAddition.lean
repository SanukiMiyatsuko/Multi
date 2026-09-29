import Multi.term3.Denis.NormalSuccessors
import Multi.term3.Denis.TransfiniteRules

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem leading_eq_of_principal (a : Term) (ha : a.isPrincipal) : a.leading = a := by
  cases a <;> first | rfl | exact False.elim ha

theorem normal_leading_le (s : OCF.Denis.Supply) (a : Term) :
    denote s a.leading ≤ denote s a := by
  induction a with
  | zero | I _ _ _ _ | psi _ _ _ _ => exact le_refl _
  | add a b iha _ => exact OCF.Ordinal.le_trans iha (le_add _ _)

theorem normal_leading_principal (s : OCF.Denis.Supply) (a : Term) (ha : IsNormal s a)
    (hne : a ≠ .zero) : AddPrincipal (denote s a.leading) := by
  cases ha with
  | zero => exact False.elim (hne rfl)
  | index => exact OCF.Denis.I_addPrincipal s _ _
  | collapse _ _ hk _ => exact OCF.Denis.psi_addPrincipal s _ _ (OCF.Denis.regularIndex_regular s _ hk)
  | @sum u v _ _ hup hp _ _ =>
    change AddPrincipal (denote s u.leading)
    rw [leading_eq_of_principal u hup]
    exact hp

theorem normal_lt_of_leading_lt (s : OCF.Denis.Supply) (a : Term) (ha : IsNormal s a)
    (k : OCF.Denis.O) (hk : AddPrincipal k) (hlt : denote s a.leading < k) : denote s a < k := by
  induction ha with
  | zero | index _ _ _ _ _ _ | collapse _ _ _ _ _ _ => exact hlt
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    change denote s u.leading < k at hlt
    rw [leading_eq_of_principal u hup] at hlt
    exact hk _ _ hlt (ihv (OCF.Ordinal.lt_of_le_of_lt hhead hlt))

/-- Ordinal addition with the absorbed tail removed, preserving right association. -/
def addTerm (s : OCF.Denis.Supply) : Term → Term → Term
  | a, .zero => a
  | .zero, b => b
  | .add u v, b => if denote s u < denote s b.leading then b else .add u (addTerm s v b)
  | a, b => if denote s a < denote s b.leading then b else .add a b

theorem addTerm_leading (s : OCF.Denis.Supply) (a b : Term) :
    (addTerm s a b).leading = a.leading ∨ (addTerm s a b).leading = b.leading := by
  cases b <;> cases a <;> simp only [addTerm] <;> first
    | simp
    | (split <;> simp [Term.leading])

theorem addTerm_ne_zero (s : OCF.Denis.Supply) (a b : Term) (hb : b ≠ .zero) :
    addTerm s a b ≠ .zero := by
  cases b <;> cases a <;> simp only [addTerm] <;> first
    | exact False.elim (hb rfl)
    | (intro h; cases h)
    | (split <;> intro h <;> cases h)

theorem addTerm_normal (s : OCF.Denis.Supply) (a b : Term) (ha : IsNormal s a)
    (hb : IsNormal s b) : IsNormal s (addTerm s a b) := by
  by_cases hbz : b = .zero
  · subst b
    simpa only [addTerm] using ha
  have hbpos := normal_denote_pos s b hb hbz
  induction ha with
  | zero => cases b <;> first | exact False.elim (hbz rfl) | exact hb
  | @index r c hr hc hrl hcl ihr ihc =>
    have ha : IsNormal s (.I r c) := .index hr hc hrl hcl
    have heq : addTerm s (.I r c) b =
        if denote s (.I r c) < denote s b.leading then b else .add (.I r c) b := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · exact hb
    · rename_i h
      exact .sum ha hb (by trivial) (OCF.Denis.I_addPrincipal s _ _) hbpos
        ((not_lt_iff_le _ _).mp h)
  | @collapse k c hk hc hreg harg ihk ihc =>
    have ha : IsNormal s (.psi k c) := .collapse hk hc hreg harg
    have heq : addTerm s (.psi k c) b =
        if denote s (.psi k c) < denote s b.leading then b else .add (.psi k c) b := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · exact hb
    · rename_i h
      exact .sum ha hb (by trivial)
        (OCF.Denis.psi_addPrincipal s _ _ (OCF.Denis.regularIndex_regular s _ hreg)) hbpos
        ((not_lt_iff_le _ _).mp h)
  | @sum u v hu hv hup hp hvpos hhead ihu ihv =>
    have heq : addTerm s (.add u v) b =
        if denote s u < denote s b.leading then b else .add u (addTerm s v b) := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · exact hb
    · rename_i h
      apply IsNormal.sum hu ihv hup hp
        (normal_denote_pos s _ ihv (addTerm_ne_zero s v b hbz))
      rcases addTerm_leading s v b with heq | heq
      · rw [heq]; exact hhead
      · rw [heq]; exact (not_lt_iff_le _ _).mp h

theorem denote_addTerm (s : OCF.Denis.Supply) (a b : Term) (ha : IsNormal s a)
    (hb : IsNormal s b) : denote s (addTerm s a b) = denote s a + denote s b := by
  by_cases hbz : b = .zero
  · subst b
    simp only [addTerm, denote, add_zero]
  have hp := normal_leading_principal s b hb hbz
  have hlead := normal_leading_le s b
  induction ha with
  | zero => cases b <;> first | exact False.elim (hbz rfl) | exact (zero_add _).symm
  | @index r c hr hc hrl hcl ihr ihc =>
    have heq : addTerm s (.I r c) b =
        if denote s (.I r c) < denote s b.leading then b else .add (.I r c) b := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · rename_i h; exact (hp.absorb_of_le h hlead).symm
    · rfl
  | @collapse k c hk hc hreg harg ihk ihc =>
    have heq : addTerm s (.psi k c) b =
        if denote s (.psi k c) < denote s b.leading then b else .add (.psi k c) b := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · rename_i h; exact (hp.absorb_of_le h hlead).symm
    · rfl
  | @sum u v hu hv hup hprin hvpos hhead ihu ihv =>
    have heq : addTerm s (.add u v) b =
        if denote s u < denote s b.leading then b else .add u (addTerm s v b) := by
      cases b <;> first | exact False.elim (hbz rfl) | rfl
    rw [heq]
    split
    · rename_i h
      have hvlt := normal_lt_of_leading_lt s v hv _ hp (OCF.Ordinal.lt_of_le_of_lt hhead h)
      exact (hp.absorb_of_le (hp _ _ h hvlt) hlead).symm
    · change denote s u + denote s (addTerm s v b) = (denote s u + denote s v) + denote s b
      rw [ihv, add_assoc]

theorem represented_add (s : OCF.Denis.Supply) (a b : OCF.Denis.O)
    (ha : Represented s a) (hb : Represented s b) : Represented s (a + b) := by
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  exact ⟨addTerm s u v, addTerm_normal s u v hu hv, denote_addTerm s u v hu hv⟩

theorem add_dense (s : OCF.Denis.Supply) (b a : OCF.Denis.O)
    (hb : Represented s b) (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a) :
    DenseBelow s (b + a) := by
  have hf := revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd
  exact dense_of_normal_sequence s _ _ (OCF.Denis.add_fundamentalSequence b a _ hf)
    (fun n => represented_add s b _ hb (revisedValue_represented s a n))

theorem I_dense (s : OCF.Denis.Supply) (r a : OCF.Denis.O)
    (hr : Represented s r) (ha : OCF.Denis.IsLimit a) (hd : DenseBelow s a) :
    DenseBelow s (OCF.Denis.I s r a) := by
  have hf := revised_fundamentalSequence_of_dense s a ((zero_lt_iff_ne_zero a).mpr ha.1) hd
  exact I_dense_of_normal_sequence s r a hr _ hf (revisedValue_represented s a)

end
end T.Correspondence.Denis.Covering
