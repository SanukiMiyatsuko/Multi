import Multi.term2.Term2Consequences
import Multi.term2.Constructive.Term2Closure

namespace T.Constructive

/-- Constructive well-foundedness from relative fundamental-sequence reductions. -/
theorem NF_is_wellfounded : WellFounded fun x y : T.NF => x.1 < y.1 :=
  normalForms_wellFounded

theorem OT_is_NF (s : T) : T.isOT s ↔ T.isNF s ∧ s < P (P Z Z Z) Z Z :=
  T.OT_is_NF_of_wellFounded NF_is_wellfounded s

theorem OT_is_wellfounded : WellFounded fun x y : T.OT => x.1 < y.1 :=
  T.OT_wellFounded_of_NF_wellFounded NF_is_wellfounded

def T.OT1Step (a b : T.OT) : Prop :=
  b.val ≠ T.Z ∧ ∃ n : Nat, a.val = T.fund b.val (T.ofNat n)

abbrev T.OT1FundLt : T.OT → T.OT → Prop :=
  FundOrder.TransClosure T.OT1Step

theorem OT1Step_lt {a b : T.OT} (h : T.OT1Step a b) :
    a.val < b.val := by
  obtain ⟨hb, n, hn⟩ := h
  rw [hn]
  exact T.fund_ofNat_lt b.val n hb

theorem T.OT1FundLt_lt {a b : T.OT} (h : T.OT1FundLt a b) :
    a.val < b.val := by
  induction h with
  | single hstep => exact OT1Step_lt hstep
  | tail _ hstep ih => exact T.lt_trans _ _ _ ih (OT1Step_lt hstep)

theorem T.OT1FundLt_of_lt (a b : T.OT) (hab : a.val < b.val) :
    T.OT1FundLt a b := by
  induction b using OT_is_wellfounded.induction with
  | h b ih =>
    have hb := (OT_is_NF b.val).mp b.property
    have ha := (OT_is_NF a.val).mp a.property
    have hbne : b.val ≠ T.Z := by
      intro heq
      rw [heq] at hab
      exact lt_Z_inv a.val hab
    obtain ⟨n, hn⟩ := T.fund_cofinal_below_omega_one b.val a.val hb.1 ha.1 hb.2 hab
    let c : T.OT := ⟨T.fund b.val (T.ofNat n), T.isOT.step b.val b.property n⟩
    have hstep : T.OT1Step c b := ⟨hbne, n, rfl⟩
    cases hn with
    | inl hlt => exact FundOrder.TransClosure.tail (ih c (OT1Step_lt hstep) hlt) hstep
    | inr heq =>
      have hac : a = c := Subtype.ext heq
      rw [hac]
      exact FundOrder.TransClosure.single hstep

theorem T.OT1FundLt_iff_lt (a b : T.OT) :
    T.OT1FundLt a b ↔ a.val < b.val := by
  exact ⟨T.OT1FundLt_lt, T.OT1FundLt_of_lt a b⟩

end T.Constructive
