import Multi.term3.Denis.SequenceAssembly

/-! Jäger-style closures (G. Jäger, Arch. math. Logik 24 (1984), clause (C5)).

The closure `C` of this project admits a collapse `psi k b` for every
argument `b` below the cutoff. Jäger's definition admits only collapses in
normal form. `PC` below admits a collapse only through a *proper*
presentation, i.e. index and argument both belong to the collapse's own
defining closure. `C` and `psi` themselves are unchanged.

For `PC`, argument and index recovery follows from the uniqueness of proper
presentations exactly as in Jäger's Lemma 4.14(d). The statement that every
element of `C` already has such a derivation is the explicit proposition
`ProperClosureComplete`. It is not assumed; its consequence for the general
argument recovery in `C` is proved here. -/

namespace OCF.Denis
open Ordinal
noncomputable section

/-- A collapse is proper when its index and argument both belong to the
closure which defines it. -/
def ProperCollapse (s : Supply) (k b : O) : Prop :=
  RegularIndex s k ∧ C s b (psi s k b) k ∧ C s b (psi s k b) b

inductive PC (s : Supply) (a beta : O) : O → Prop where
  | zero : PC s a beta 0
  | seed {x : O} : x < beta → PC s a beta x
  | add {x y : O} : PC s a beta x → PC s a beta y → PC s a beta (x + y)
  | index {x y : O} : PC s a beta x → PC s a beta y → PC s a beta (I s x y)
  | collapse {k b : O} : b < a → ProperCollapse s k b →
      PC s a beta k → PC s a beta b → PC s a beta (psi s k b)

theorem PC.sub_C {s : Supply} {a beta x : O} (h : PC s a beta x) : C s a beta x := by
  induction h with
  | zero => exact C_zero s a beta
  | seed hx => exact C_seed s a beta _ hx
  | add _ _ ihx ihy => exact C_add s a beta _ _ ihx ihy
  | index _ _ ihx ihy => exact C_index s a beta _ _ ihx ihy
  | collapse hb hp _ _ ihk ihb => exact C_collapse s a beta _ _ hb hp.1 ihk ihb

theorem PC.mono {s : Supply} {a b beta gamma : O} (hab : a ≤ b) (hbg : beta ≤ gamma)
    {x : O} (h : PC s a beta x) : PC s b gamma x := by
  induction h with
  | zero => exact .zero
  | seed hx => exact .seed (lt_of_lt_of_le hx hbg)
  | add _ _ ihx ihy => exact .add ihx ihy
  | index _ _ ihx ihy => exact .index ihx ihy
  | collapse hb hp _ _ ihk ihb => exact .collapse (lt_of_lt_of_le hb hab) hp ihk ihb

theorem PC_finite (s : Supply) (a beta : O) (ha : 0 < a) (n : Nat) : PC s a beta (finite n) := by
  have hone : PC s a beta (succ 0) := by
    have hp : ProperCollapse s (I s 0 0) 0 :=
      ⟨Or.inl ⟨0, rfl⟩, first_mem_C s 0 _, C_zero s 0 _⟩
    have h := PC.collapse (s := s) (a := a) (beta := beta) ha hp (.index .zero .zero) .zero
    rwa [psi_first_zero] at h
  induction n with
  | zero => exact .zero
  | succ n ih =>
    have h := PC.add ih hone
    change PC s a beta (succ (finite n))
    rwa [add_succ, add_zero] at h

/-- Jäger's Lemma 4.14(d) for `PC`: a proper collapse above the seed has
its own index and argument in the closure, with the argument below the
cutoff. The argument may be arbitrarily large compared to the index. -/
theorem PC_proper_collapse_parameters (s : Supply) (k a cutoff beta : O)
    (hp : ProperCollapse s k a) (hb : beta ≤ psi s k a)
    (hx : PC s cutoff beta (psi s k a)) :
    a < cutoff ∧ PC s cutoff beta k ∧ PC s cutoff beta a := by
  have hreg := regularIndex_regular s k hp.1
  have hprin := psi_addPrincipal s k a hreg
  have hpos : 0 < psi s k a := psi_pos s k a (regular_pos hreg)
  have aux (y : O) (hy : PC s cutoff beta y) :
      y = psi s k a → a < cutoff ∧ PC s cutoff beta k ∧ PC s cutoff beta a := by
    induction hy with
    | zero =>
      intro heq
      rw [← heq] at hpos
      exact False.elim (lt_irrefl _ hpos)
    | seed hy =>
      intro heq
      rw [heq] at hy
      exact False.elim (lt_irrefl _ (lt_of_lt_of_le hy hb))
    | @add u w hu hw ihu ihw =>
      intro heq
      rcases addPrincipal_suffix hprin heq.symm with hw0 | hweq
      · rw [hw0, add_zero] at heq
        exact ihu heq
      · exact ihw hweq
    | @index u w hu hw ihu ihw =>
      intro heq
      rcases rank_le_I s u w with hur | hur
      · rcases index_le_I s u w with hwr | hwr
        · exact False.elim (I_normal_ne_psi s u w k a hreg hur hwr heq)
        · exact ihw (hwr.trans heq)
      · exact ihu (hur.trans heq)
    | @collapse l b hbc hq hl hbP ihl ihb =>
      intro heq
      obtain ⟨hlk, hba⟩ := psi_normal_parameters_unique s l b k a hq.1 hp.1 hq.2.1 hq.2.2
        hp.2.1 hp.2.2 heq
      subst hlk
      subst hba
      exact ⟨hbc, hl, hbP⟩
  exact aux _ hx rfl

/-- Every element of the project's closure has a derivation using only
proper collapses. This is the missing completeness statement; it is an
explicit proposition, not an axiom or instance. -/
def ProperClosureComplete (s : Supply) : Prop :=
  ∀ a beta x, C s a beta x → PC s a beta x

/-- General argument recovery in the project's closure, with no bound of
the argument by its index, from the completeness statement. -/
theorem C_proper_collapse_parameters_of_complete (s : Supply) (hcomplete : ProperClosureComplete s)
    (k a cutoff beta : O) (hp : ProperCollapse s k a) (hb : beta ≤ psi s k a)
    (hx : C s cutoff beta (psi s k a)) :
    a < cutoff ∧ C s cutoff beta k ∧ C s cutoff beta a := by
  obtain ⟨hac, hk, ha⟩ := PC_proper_collapse_parameters s k a cutoff beta hp hb
    (hcomplete _ _ _ hx)
  exact ⟨hac, hk.sub_C, ha.sub_C⟩

end
end OCF.Denis
