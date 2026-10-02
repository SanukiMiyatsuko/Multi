# 大きい極限段階 `LargeLimitCoveringStep`（証明済み）

正規な ψk(a)（a は極限で非可算正則ではなく、k ≤ a、k ∈ C(a, ψk a)）について、
最小長の被覆基本列 `HasCoveringSequence` が存在する。
OCF の `C` と `psi` の定義は変更していない。

**主定理（`LargeLimitStep.lean`、名前空間 `T.Correspondence.Denis.Covering`）**

- `largeLimitCoveringStep_holds`: `LargeLimitCoveringStep s`。
- `normal_hasCoveringSequence`: **すべての正規項**の値が、共終数を長さとする被覆基本列を持つ。
  正規な添字の値は正規形で表せ、親未満の任意の正規値を正規な添字の項で上回る。
- `normal_hasNormalSequence`: すべての正規項が最小長の正規基本列を持つ。
- `properLimitStep_holds`, `properRemainingLimitStep_holds`: 以前の定式化の残りの帰納段階も成り立つ。
- `normal_dense_of_cofinality_omega`: 共終数 ω の正規な極限項では、正規形の値が実際の順序数で
  稠密（`DenseBelow`）である。
- `normal_revised_cofinal_of_cofinality_omega`: 共終数 ω の正規な極限項では、
  自然数添字の修正展開 `revisedValue` が**実際の順序数で共終**である。

非可算の共終数では自然数添字の展開は共終になりえない（`DenseBelow` は成立しない）。
その場合の基本列は順序数添字の `normal_hasCoveringSequence` で与える。

公理は propext・Quot.sound・Classical.choice のみ（`ProofAuditTerm3Denis.lean` で監査済み）。

## 証明の構成

| 段階 | 内容 | 主な定理 | ファイル |
|---|---|---|---|
| 1 | 非孤立の場合: c<a で常に ψk(c)<ψk(a) なら、a の被覆列を c↦ψk(c) で移す | `hasCoveringSequence_psi_nonisolated` | LargeLimitCases.lean |
| 2 | 孤立の場合を段階上界 `IsolatedStageBound` に帰着（対角列） | `hasCoveringSequence_psi_diagonal`, `isolatedLargeLimitStep_of_stageBound` | IsolatedDiagonal.lean |
| 3 | 閉包の標準分解・閉包の上限・分離値の一様な所属・対角反復 | `C_canonical`, `supBelow`, `sep_mem`, `stage_iteration` | StageBasics.lean |
| 4 | 一様段階上界 `UStage`: 正則値・和・極限引数の I | `ustage_regular`, `ustage_sum`, `ustage_I_limit` | UniformStage.lean |
| 5 | 極限引数の崩壊 | `ustage_psi_limit` | UniformStageLimit.lean |
| 6 | 零・後続引数の崩壊（添字の rank が極限） | `ustage_psi_rank` | UniformStageRank.lean |
| 7 | 正規項のサイズに関する帰納法と全体の組み立て | `ustage_normal`, `isolatedStageBound_of_ustage` | LargeLimitStep.lean |

一般の引数回収（[ARGUMENT_RECOVERY.md](ARGUMENT_RECOVERY.md)）と、
天井帰納法の分離値の不変量（`CeilCtx.inv_all`）を全体で使う。
`Barrier.lean` の障壁補題 `C_barrier`（ψk(e)≤x<ψk(e+1) の閉包所属から e を回収する）も証明したが、
最終的な証明では分離値の議論で置き換えた。

## 孤立の場合

D=C(a,ψk a) とする。ある c<a で ψk(c)=ψk(a) なら、プラトー補題により D は [c,a) に元を持たない。
D に属す正規な y<a ごとに、段階閉包 C(y,ψk y) の a 未満の部分を上から抑える
正規な y'∈D∩a があれば（`IsolatedStageBound`）、0 から反復した列 yₙ について
C(a, sup ψk(yₙ)) が段階閉包の和に含まれる。よって ψk(a)=sup ψk(yₙ) であり、
i↦ψk(yᵢ)+i が長さ ω の被覆基本列になる。

## 一様段階上界 `UStage`

`OCF.Denis.UStage s x` は次を主張する。x が Y=C(A,ψκ A) で孤立している
（`IsoIn`: x は極限で、Y はある c<x 以上 x 未満に元を持たない）とき、任意の y<A について、
C(y,ψκ y) の x 未満の元をすべて上から抑える w<x がある。
さらに同じ w は、x・y・κ を含み切断点が y より大きい**任意の閉包**に属す。

この一様性から、w が D に属すことと、切断点を大きくとった C(A',0) に属すこと、
すなわち正規形で表せることが同時に従う。
孤立した引数 a 自身に適用すると `IsolatedStageBound` になる。

各場合の上界は次のとおり。

- **正則値** x: w=ψx(y)。κ≤x は孤立性から従う。
- **和** p+q: q も孤立し、w=p+w_q。上界の確認には後半の回収 `C_suffix` を使う。
- **極限引数の I(r,z)**: z も孤立し、w=I(r,w_z)。I 区間の回収 `C_I_interval` を使う。
- **極限引数の崩壊** ψπ(e)（proper）:
  1. e より小さい引数で同じ値にはならない。もしそうなら e は自身の閉包 C(e,ψπ e) で孤立する。
     そこで e の一様上界を反復すると、一様性により Y の元の列が得られ、
     その崩壊値が x に共終になって x の孤立性に反する。
  2. 連続性により e は Y で孤立し、e の上界 We が得られる。
  3. w は、π のパラメータ・段階の種 ψκ(y)・ψπ(We) の和 m を超える最小の ψπ(f)
     （f は C(e,x) の元）とする。
     天井帰納法の分離値の不変量により、w は m と π を含む任意の閉包に属す（`sep_mem`）。
     段階閉包の最小の反例を考えると、どの形も成立しない。
     和と I の値は ψ 値を超えない。小さい添字の崩壊は、その添字自体が上界未満である。
     同じ添字なら引数が We 未満になる。大きい添字なら π が反例未満で生成される。
- **零・後続引数の崩壊** ψπ(e)、π=I(λ,ζ): σ を Y の x 未満の上限とする。
  x の最小性から、C(e,σ) の [σ,π) における最小元は I(b₁,b₂) の形
  （b₁,b₂<σ）にしかなりえない。これから b₁<λ かつ Y∩[b₁,λ)=∅ が従う。
  よって λ は Y で孤立した極限であり、λ の上界 wλ を使って
  w=I(wλ,L+1) とする。ここで L=λ+ζ+I(λ,ζ')+ψπ(e')+ψκ(y)
  （ζ=ζ'+1、e=e'+1 の場合の項）である。
- **添字所属が欠ける崩壊**: 値を保ちサイズを減らす書き換え（`smaller_of_index_not_mem`）で
  帰納法に戻す。
