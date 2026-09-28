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
  sorry

theorem T.OT1FundLt_lt {a b : T.OT} (h : T.OT1FundLt a b) :
    a.val < b.val := by
  sorry

theorem T.OT1FundLt_of_lt (a b : T.OT) (hab : a.val < b.val) :
    T.OT1FundLt a b := by
  sorry

theorem T.OT1FundLt_iff_lt (a b : T.OT) :
    T.OT1FundLt a b ↔ a.val < b.val := by
  exact ⟨T.OT1FundLt_lt, T.OT1FundLt_of_lt a b⟩

end T.Constructive
