# 一般の引数回収（証明済み）

`LargeLimitCoveringStep` の証明には、添字以上の引数を持つ崩壊 ψk(b) について
「ψk(b) ∈ C(a,β)（β ≤ ψk(b)）なら b ∈ C(a,β)」という引数回収が必要だった。
OCF の `C` と `psi` の定義は変更していない。

**主定理（`CeilingInduction.lean`）**

- `OCF.Denis.properClosureComplete`: Denis の閉包 C(a,β) の元はすべて、
  proper な崩壊（添字と引数がともに自身の定義閉包に属する崩壊）だけを使う
  Jäger 型閉包 PC(a,β) の導出を持つ。
- `OCF.Denis.C_proper_collapse_parameters`: (k,b) が proper で β ≤ ψk(b)、
  ψk(b) ∈ C(a,β) なら b < a かつ k, b ∈ C(a,β)。**引数を添字で上から抑える条件はない。**
- `T.Correspondence.Denis.Covering.normal_representedClosureStage`（`NormalClosureStage.lean`）:
  極限 a に対し、C(a,ψk a) に属する任意の正規項の値は、正規形で表せる c<a の段階
  C(c,ψk c) にすでに属す。従来の `CollapseTree` への制限はなくなった。

公理は propext・Quot.sound・Classical.choice のみ（監査済み）。

## 証明の構成

| 段階 | 内容 | 主な定理 | ファイル |
|---|---|---|---|
| 1 | Jäger 型閉包 PC と PC での引数回収（Jäger 4.14(d) の類似） | `PC_proper_collapse_parameters` | ProperClosure.lean |
| 2 | I の不動点と I 区間回収 | `I_rank_fixed`, `C_I_interval`, `PC_I_interval` | ClosureIntervals.lean |
| 3 | 隙間補題と一般の添字回収 | `C_index_gap`, `C_index_of_collapse_value` | IndexGap.lean |
| 4 | 引数プラトー | `psi_proper_plateau`, `proper_parameters_at_presentation` | PlateauGap.lean |
| 5 | 完全性を崩壊1回の閉包性（天井補題）に帰着 | `collapse_closed_of_ceiling`, `plateau_top`, `index_ceiling` | CompletenessReduction.lean |
| 6 | 極限引数での ψ の連続性と後者引数での跳躍 | `psi_limit_le`, `argument_mem_of_psi_succ_gt` | CollapseContinuity.lean |
| 7 | 天井と分離値の基本補題 | `IsCeil.canonical`, `IsSep.of_index` など | CeilingBasics.lean, Separation.lean |
| 8 | 天井不変量の帰納法と完全性 | `CeilCtx.inv_all`, `pcCollapseStep_holds` | CeilingInduction.lean |

段階5: γ=ψk(b)、D=C(b,γ) とすると、b の D における天井 b*（D の元で b 以上の最小）と
γ の天井 k* から γ の proper な表示 (k*,b*) が得られる。k* は隙間補題で回収できる。

段階8: X=PC(a,β) の各元 y について、次の2つを y の導出に関する帰納法で同時に示す
（和の接尾辞にも一般化する）。崩壊引数に関する外側の帰納法により、
D の引数 d<b での崩壊は X に閉じていると仮定してよい。

- 天井: y の D における天井は X に属す。
- 分離: D の正則添字 κ∈X に対し、y を超える最小の値 ψκ(d)（d は D の引数）は X に属す。

天井が I 値の場合は、成分の天井、`PC_I_interval`、D 側の I 区間回収で閉じる。
天井が ψ 値で y が I 値の場合は、まず天井の添字 κ を X に回収し、
天井が y の分離値であることから成分の分離値に帰着する。
分離値の計算では、種（β 未満）の場合に ψ の極限での連続性を使う。
これにより、超えるべき最小の引数は後者 e'+1 となり、
跳躍補題から e' ∈ C(e',ψκe') ⊆ C(e',β) が従う。

## その後の利用

この引数回収と天井帰納法の分離値の不変量を使い、`LargeLimitCoveringStep` 自体を
`LargeLimitStep.lean` の `largeLimitCoveringStep_holds` で証明した。
詳細は [LARGE_LIMIT_STEP.md](LARGE_LIMIT_STEP.md)。
