# Status: target theorem NOT proved

Goal: constructive `T.OT_is_wellfounded` for `Multi/Term3.lean`.
Only `propext`, `Quot.sound`; no mathlib, no opaque automated proof tactics,
no original definition changes. Helpers use `theorem`.

User has no separate mathematical definition or normal-form reference for Term3.
Do not spawn subagents. The user deleted the old `Multi/term2.lean` entry independently;
do not restore it as part of this task. Actual target file uses uppercase `Term3.lean`.

## Verified source modules

- `Multi/Term3Syntax.lean`: copied original declarations excluding the target;
  `fund` termination proof changed from `all_goals first` to 20 explicit `exact` goals.
  Original declaration equations and types unchanged.
- `Multi/Constructive/Term3Fundamental.lean`: 307 lines, compiles.
  Proves dom=Zero iff sourceZero (one direction currently),
  large-domain index cases: `dom l1=One` or `l1=Z ∧ dom l0=One`,
  raw fundamental descent for all admissible inputs, natural input admissibility,
  and all OT terms below `P Z (P Z Z Z Z) Z Z`.
- `Multi/Constructive/Term3Normal.lean`: compiles. New auxiliary definitions
  `head`, `G₁`, `G₂`, `isNF`, `NF`; proves component/support properties,
  all base terms normal, normal domain marker normal and ≤ source head,
  no large domain for normal terms below first uncountable marker.
- `Multi/Term3.lean` currently imports Fundamental and retains the original target
  with `by sorry`. It is NOT finished. Normal is not yet in its import chain.

## Current candidate normal forms

For `P a b c d`, all components normal, `head d ≤ P a b c Z`,
every `x ∈ G₁ a b` satisfies `x<b`, and every `x ∈ G₂ a b c` satisfies `x<c`.

`G₁ u (P a b c d)`:
- if `u≤a`: `[b] ++ G₁ u a ++ G₁ u b ++ G₁ u d`
- otherwise `G₁ u d`.
It deliberately does not descend into the third coordinate.

`G₂ u v (P a b c d)`:
- if `P u v Z Z ≤ P a b Z Z`:
  `[b,c] ++ G₂ u v a ++ G₂ u v b ++ G₂ u v c ++ G₂ u v d`
- otherwise `G₂ u v d`.
Both `b` and `c` must be recorded. Preservation by `fund` is NOT yet proved.

## Exploration, not formal proofs

Python runtime:
`C:/Users/Owner/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Scratch evaluator `.lake/term3-explore.py` uses tuples for raw terms, memoized dom/fund.
Its original main tests a failed simple ternary encoding; do not confuse its
failure with a counterexample to the goal.

- Simple grouping into Term2 (`P(P(Ea)(Eb)0)(Ec)(Ed)`) does not preserve NF on OT.
- First G₁ attempt recursed into c: failed for generated OT, so c removed.
- First G₂ attempt collected only c: preservation fails for
  `s = h(f(P 1 1 0 0))`, input 2, result `h(f(P 1 0 q 0))`,
  where `h x=P 0 0 x 0`, `f x=P 0 x 0 0`, `q=P 1 0 0 0`.
  Adding b to G₂ fixes this tested counterexample by excluding the source.
- Current candidate: all 4352 NF terms of size ≤6 preserve NF and monotonicity
  for natural inputs 0..3 in the Python finite test. Also passes first 15000
  distinct OT terms generated from bases 0..4 with inputs0..4 and bounded depth/size.
  This finite evidence is NOT a proof of normality preservation or well-foundedness.
- Attempted search for infinite descending chains found no counterexample.
  `.lake/term3-chain-explore.py` last run completed at 300000 terms.

## Next proof obligations

1. Prove fundamental-sequence preservation of the candidate NF (and adjust
   auxiliary NF definitions if a genuine obstruction appears).
2. Prove cofinality/commutation/bracketing appropriate to two domain coordinates.
3. Adapt generic `Multi/Constructive/Stages.lean` (imports nothing) distinguished
   set argument, or another constructive proof. Term2-specific modules cannot
   be imported with Term3 because they also define global `T` with different arity.
4. Show all NF well-founded, or at least accessible base terms and enough
   downward closure to prove the original OT theorem.
5. Replace original target sorry only with a complete kernel-checked proof;
   audit target axioms, all import dependencies and original definitions.

The first-coordinate successor regular marker `P (a+1) Z Z Z` is harder than
Term2: regular markers below it have unbounded second coordinate. The simple
Term2 locality argument below `Ω(a+1)` cannot be copied verbatim.

Audits: `.lake/check-term3-definitions.ps1`, `.lake/term3-foundation-audit.lean`.
Lean commands need `$env:ELAN_HOME = 'C:/Users/Owner/.elan'`.
