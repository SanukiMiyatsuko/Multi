import Multi.term3.Denis.RevisedCofinality

namespace OCF.Denis
open Ordinal

theorem addPrincipal_succ_pred_zero (a : O) (h : AddPrincipal (succ a)) : a = 0 := by
  classical
  by_cases hz : a = 0
  · exact hz
  · have ha := (zero_lt_iff_ne_zero a).mpr hz
    have hone : succ 0 < succ a := lt_of_le_of_lt ((succ_le_iff_lt 0 a).mpr ha) (lt_succ_self a)
    have hh := h a (succ 0) (lt_succ_self a) hone
    rw [add_succ, add_zero] at hh
    exact False.elim (lt_irrefl _ hh)

theorem add_isLimit (a b : O) (hb : IsLimit b) : IsLimit (a + b) := by
  have hbpos := (zero_lt_iff_ne_zero b).mpr hb.1
  refine ⟨(zero_lt_iff_ne_zero _).mp (lt_of_lt_of_le hbpos (right_le_add a b)), ?_⟩
  rintro ⟨c, hc⟩
  have hclt : c < a + b := hc ▸ lt_succ_self c
  rcases (lt_add_iff a b c).mp hclt with hca | ⟨d, hd, hcd⟩
  · have ha : a < a + b := by
      have hh := add_lt_add_right a hbpos
      rwa [add_zero] at hh
    rw [hc, lt_succ_iff_le] at ha
    exact lt_irrefl _ (lt_of_lt_of_le hca ha)
  · have hcy : c < a + succ d := lt_of_le_of_lt hcd (add_lt_add_right a (lt_succ_self d))
    have hya := add_lt_add_right a (succ_lt_limit hb hd)
    rw [hc, lt_succ_iff_le] at hya
    exact lt_irrefl _ (lt_of_lt_of_le hcy hya)

theorem right_is_succ_of_add_succ (a b c : O) (hb : b ≠ 0) (h : a + b = succ c) :
    ∃ d, b = succ d := by
  classical
  by_cases hs : ∃ d, b = succ d
  · exact hs
  · exact False.elim ((add_isLimit a b ⟨hb, hs⟩).2 ⟨c, h⟩)

end OCF.Denis

namespace T.Correspondence.Denis.Covering
open OCF.Ordinal
noncomputable section

theorem normal_denote_pos (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) (hne : t ≠ .zero) :
    0 < denote s t := by
  cases ht with
  | zero => exact False.elim (hne rfl)
  | index _ _ _ _ =>
    exact OCF.Ordinal.lt_of_lt_of_le (OCF.Denis.regular_pos (OCF.Denis.first_regular s))
      (OCF.Denis.I_lower_bound s _ _)
  | collapse _ _ hk _ =>
    exact OCF.Denis.psi_pos s _ _ (OCF.Denis.regular_pos (OCF.Denis.regularIndex_regular s _ hk))
  | sum _ _ _ _ hb _ => exact OCF.Ordinal.lt_of_lt_of_le hb (right_le_add _ _)

def succTerm : Term → Term
  | .zero => one
  | .add a b => .add a (succTerm b)
  | a => .add a one

theorem denote_succTerm (s : OCF.Denis.Supply) (t : Term) : denote s (succTerm t) = succ (denote s t) := by
  induction t with
  | zero => exact denote_one s
  | add a b iha ihb =>
    change denote s a + denote s (succTerm b) = _
    rw [ihb, add_succ]
    rfl
  | I a b iha ihb | psi a b iha ihb =>
    change _ + denote s one = _
    rw [denote_one, add_succ, add_zero]

theorem leading_succTerm (t : Term) (h : t ≠ .zero) : (succTerm t).leading = t.leading := by
  cases t with
  | zero => exact False.elim (h rfl)
  | add a b => rfl
  | I a b => rfl
  | psi a b => rfl

theorem succTerm_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) : IsNormal s (succTerm t) := by
  induction ht with
  | zero => exact one_isNormal s
  | @index r b hr hb hrl hbl ihr ihb =>
    have ht := IsNormal.index hr hb hrl hbl
    apply IsNormal.sum ht (one_isNormal s) (by trivial) (OCF.Denis.I_addPrincipal s _ _)
    · rw [denote_one]; exact lt_succ_self 0
    · change denote s one ≤ denote s (.I r b)
      rw [denote_one]
      exact (succ_le_iff_lt _ _).mpr (normal_denote_pos s _ ht (by intro h; cases h))
  | @collapse k a hk ha hreg harg ihk iha =>
    have ht := IsNormal.collapse hk ha hreg harg
    apply IsNormal.sum ht (one_isNormal s) (by trivial)
      (OCF.Denis.psi_addPrincipal s _ _ (OCF.Denis.regularIndex_regular s _ hreg))
    · rw [denote_one]; exact lt_succ_self 0
    · change denote s one ≤ denote s (.psi k a)
      rw [denote_one]
      exact (succ_le_iff_lt _ _).mpr (normal_denote_pos s _ ht (by intro h; cases h))
  | @sum a b ha hb hap hprin hbpos hhead iha ihb =>
    apply IsNormal.sum ha ihb hap hprin
    · rw [denote_succTerm]
      exact OCF.Ordinal.lt_trans _ _ _ hbpos (lt_succ_self _)
    · have hbne : b ≠ .zero := by intro h; cases h; exact OCF.Ordinal.lt_irrefl _ hbpos
      rw [leading_succTerm b hbne]
      exact hhead

theorem represented_succ (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : Represented s a) :
    Represented s (succ a) := by
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨succTerm t, succTerm_normal s t ht, denote_succTerm s t⟩

def predTerm : Term → Term
  | .add a b => if predTerm b = .zero then a else .add a (predTerm b)
  | _ => .zero

theorem leading_predTerm (t : Term) (h : predTerm t ≠ .zero) : (predTerm t).leading = t.leading := by
  cases t with
  | zero | I _ _ | psi _ _ => exact False.elim (h rfl)
  | add a b =>
    unfold predTerm
    split <;> rfl

theorem predTerm_normal (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t) : IsNormal s (predTerm t) := by
  induction ht with
  | zero | index _ _ _ _ _ _ | collapse _ _ _ _ _ _ => exact .zero
  | @sum a b ha hb hap hprin hbpos hhead iha ihb =>
    change IsNormal s (if predTerm b = .zero then a else .add a (predTerm b))
    split
    · exact ha
    · rename_i hne
      apply IsNormal.sum ha ihb hap hprin (normal_denote_pos s _ ihb hne)
      rw [leading_predTerm b hne]
      exact hhead

theorem denote_predTerm_of_succ (s : OCF.Denis.Supply) (t : Term) (ht : IsNormal s t)
    (a : OCF.Denis.O) (heq : denote s t = succ a) : denote s (predTerm t) = a := by
  induction ht generalizing a with
  | zero =>
    have hz : succ a = (0 : OCF.Denis.O) := heq.symm
    have h : a < (0 : OCF.Denis.O) := hz ▸ lt_succ_self a
    exact False.elim (not_lt_zero _ h)
  | @index r b hr hb hrl hbl ihr ihb =>
    have hp := OCF.Denis.I_addPrincipal s (denote s r) (denote s b)
    change AddPrincipal (denote s (.I r b)) at hp
    rw [heq] at hp
    exact (OCF.Denis.addPrincipal_succ_pred_zero a hp).symm
  | @collapse k b hk hb hreg harg ihk ihb =>
    have hp := OCF.Denis.psi_addPrincipal s (denote s k) (denote s b)
      (OCF.Denis.regularIndex_regular s _ hreg)
    change AddPrincipal (denote s (.psi k b)) at hp
    rw [heq] at hp
    exact (OCF.Denis.addPrincipal_succ_pred_zero a hp).symm
  | @sum u v hu hv hup hprin hvpos hhead ihu ihv =>
    have hvne := (zero_lt_iff_ne_zero _).mp hvpos
    obtain ⟨b, hb⟩ := OCF.Denis.right_is_succ_of_add_succ (denote s u) (denote s v) a hvne heq
    have hp := ihv b hb
    change denote s u + denote s v = succ a at heq
    rw [hb, add_succ] at heq
    have heqa := OCF.Denis.succ_injective heq
    change denote s (if predTerm v = .zero then u else .add u (predTerm v)) = a
    split
    · rename_i hz
      rw [hz] at hp
      change (0 : OCF.Denis.O) = b at hp
      rw [← hp, add_zero] at heqa
      exact heqa
    · change denote s u + denote s (predTerm v) = a
      rw [hp]
      exact heqa

theorem represented_predecessor (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : Represented s (succ a)) : Represented s a := by
  obtain ⟨t, ht, heq⟩ := ha
  exact ⟨predTerm t, predTerm_normal s t ht, denote_predTerm_of_succ s t ht a heq⟩

theorem revised_succ_eq (s : OCF.Denis.Supply) (a : OCF.Denis.O) (ha : Represented s a) (n : Nat) :
    revisedValue s (succ a) n = a := by
  have hp : HasPredecessor s (succ a) :=
    ⟨a, ha, lt_succ_self a, fun b _ hb => (lt_succ_iff_le b a).mp hb⟩
  rw [revisedValue_predecessor s _ hp]
  exact le_antisymm ((lt_succ_iff_le _ _).mp (predecessor_spec s _ hp).2.1)
    ((predecessor_spec s _ hp).2.2 a ha (lt_succ_self a))

theorem actual_limit_is_normalLimit (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) : NormalLimit s a := by
  refine ⟨(zero_lt_iff_ne_zero a).mpr ha.1, ?_⟩
  intro b hb hba
  exact ⟨succ b, represented_succ s b hb, lt_succ_self b, OCF.Denis.succ_lt_limit ha hba⟩

/-- All actual limit ordinals now get strictly increasing normal values;
the remaining semantic obligation is cofinality, not strictness. -/
theorem revised_strict_at_actual_limit (s : OCF.Denis.Supply) (a : OCF.Denis.O)
    (ha : OCF.Denis.IsLimit a) (n m : Nat) (h : n < m) : revisedValue s a n < revisedValue s a m :=
  revised_limit_strict s a (actual_limit_is_normalLimit s a ha) n m h

end
end T.Correspondence.Denis.Covering
