# OCF の値を維持した基本列の修正

利用者の指定は「基本列展開が OCF の正規形全体を渡るように基本列の方を修正する」である。
`Cardinals.lean`・`Collapse.lean` の OCF 定義はこの修正で変更していない。
元の規則10.5の反例は `COUNTEREXAMPLE.md` と対応する Lean 定理に保存する。

## 展開の構成

1. `terms n` で有限項を列挙する。全項がある有限段階で出現することを `terms_complete` で証明する。
2. 親 a より小さく、正規形である項の順序数値だけを候補とする。候補の有限最大値を `value s a n` とする。
3. 正規形の値の集合内で前者が存在するならそれを返す。
4. 前者がなく親が非零なら、最大値が真に増加する最初の列挙段階へ進む。`advance_minimal` が「最初」であることを証明する。
5. 出力値に対して正規形の代表項を選ぶ。

意味論と正規形判定には Classical.choice を使う非計算的な定義である。
既存の構文的比較を計算手続きとして正しいと仮定してはいない。

## 全体について証明済みの性質

| 性質 | 定理・定義 |
|---|---|
| 全有限項の列挙 | `terms_complete` |
| 非零の親からの降下 | `revisedValue_lt` |
| 正規形の出力 | `expandedTerm_normal` |
| 後続順序数の前者を返す | `represented_predecessor`, `revised_succ_eq` |
| すべての実際の極限順序数で狭義増加 | `revised_strict_at_actual_limit` |
| 正規形集合内の極限で共終 | `revised_limit_cofinal_among_normal` |
| 有限回の展開で到達する値の完全な特徴づけ | `follow_exists_iff_le` |
| rank 塔の根の族から正規形全体へ到達 | `all_normal_ordinals_reachable`, `all_normal_terms_reachable` |
| 代表選択で意味論を保存 | `denote_normalise` |
| 正規形の値を一つも失わない | `canonical_covers_normal` |
| 代表項の整列順序 | `canonicalWellOrder` |

上記の名前は `T.Correspondence.Denis.Covering` 名前空間に属する。

同じ順序数を表す異なる構文が実際に存在するため、「全体」とは順序数値としての
正規形全体を指す。等しい値の異なる綴りを、順序数の狭義降下で相互に辿ることはできない。
代表の選択はこの重複を扱うもので、表現される順序数を削らない。

## 元の順序数での共終性

正規形集合内での共終性だけから、元の順序数に共終であるとは結論しない。
`DenseBelow s a` は、任意の x<a に対して x<b<a となる正規形の値 b が存在することを表す。

- `dense_iff_revised_cofinal`：修正展開の順序数としての共終性と `DenseBelow` の同値。
- `revised_fundamentalSequence_of_dense`：この条件から降下・狭義増加・共終の3性質を導く。
- `revised_omega_fundamentalSequence`：ω の場合。
- `revised_epsilon_fundamentalSequence`：ψ_{I(0,0)}(I(0,0)) の場合。
- `revised_obstruction_fundamentalSequence`：元の規則10.5の反例の親の場合。
- `revised_collapseI_fundamentalSequence`：ψ_{I(0,0)}(I(1,0)) の場合。

`FirstInterval.lean` の `normal_dense_below_first_diagonal` は、
`psi (I 0 0) (I 0 0)` 以下のすべての正規な極限項で `DenseBelow` を証明する。
`revised_normal_below_first_diagonal_fundamentalSequence` がこの区間全体での
修正基本列の降下・狭義増加・共終性を与える。一般の可算対象での証明は未完了である。
また `not_dense_regular` は、非可算正則基数には自然数で列挙した有限記法項が
共終になれないことを証明する。この場合の基本列は順序数を添字として扱う必要がある。
正則基数の恒等基本列は `regular_fundamentalSequence` と
`regular_no_shorter_cofinal` で証明済みである。

## 共終数と順序数添字

`Cofinality.lean` では、共終な写像を持つ最小の順序数を共終数として定義し、
その長さで狭義増加する基本列 `intrinsicSequence` を整礎再帰で構成した。
任意の共終写像を対象に最小値を取っているため、増加列の中だけの最小性ではない。

| 性質 | 定理 |
|---|---|
| 最小長での降下・狭義増加・共終 | `intrinsicSequence_spec` |
| 可算基本列の最小長は ω | `cofinality_eq_omega_of_fundamentalSequence` |
| 非可算正則基数 κ の最小長は κ | `cofinality_regular` |
| 共終数自身の共終数は自身 | `cofinality_idempotent` |
| ω より大きい共終数は正則 | `cofinality_uncountableRegular` |
| 親と狭義増加共終列の添字長の共終数は一致 | `cofinality_eq_of_transfiniteFundamentalSequence` |
| 共終数を添字長とする列の長さは最小 | `cofinality_eq_of_minimal_length` |

これらの名前空間は `OCF.Denis`。一般構成の値が有限正規形で表せることは主張しない。
`TransfiniteRules.lean` は順序数添字に対する加法・I・ψの基本列保存則を証明する。
ψ の各添字での閉包所属条件は、証明すべき前提として残している。

`RevisedDomains.lean` の `NormalFundamentalSequence` は、すべての順序数添字で
降下・増加・共終性を要求し、正規形で表せる添字では出力にも正規形を要求する。
可算の場合には全添字が有限順序数なので、これは各項が正規形であることを意味する。
非可算正則基数の恒等列にも同じ仕様が適用できる。
修正可算列と恒等列の実装、加法・I・条件付き ψ による仕様の保存が証明済みである。

`NormalAddition.lean` の正規化で正規形の和を構成できるので、
既知の `DenseBelow` は `add_dense` と `I_dense` により加法と I の極限に伝播する。
また `not_dense_of_uncountable_cofinality` は、正則基数だけでなく
共終数が ω より大きい任意の親で自然数添字の候補列が不足することを示す。

`successor_rank_zero_dense` と `revised_successor_rank_zero_fundamentalSequence` は、
任意の正規形で表せる rank r に対する `psi (I (succ r) 0) 0` の族全体を扱う。
`SuccessorSequence.lean` は最初の正則添字での ψ の後続引数の枝を扱い、
引数がその添字未満なら前者の閉包所属を親の正規性から導く。
`FirstInterval.lean` はこの後続枝と極限枝・加法を組み合わせた正規項の帰納法で、
最初の対角崩壊値以下の区間全体の密度を証明する。

## 後続枝と可算尾部の極限枝

`ClosureSubterms.lean` により、以下は C の元の閉包定義から導かれる。

- `C_predecessor`：後続順序数が C に属すれば前者も属す。
- `C_suffix`：x=r+b が C に属すれば b も属す。
- `C_normal_index_parameters`：正規な I(r,b) が C に属すれば r,b も属す。
- `C_principal_prefix`：加法的主項 p と b<p について、p+b の C 所属から p の所属を得る。
- `psi_predecessor_argument_normal_general`：ψ の正規な後続引数から前者の閉包所属を得る。引数が可算であるという制限はない。

したがって `revised_psi_first_normal_successor_general` は最初の正則添字の ψ の
正規な後続枝すべてを扱う。

`CountableTails.lean` の `composite_eventual_argument_normal` は、
閉包の有限性と連続性を使って、固定パラメータを持つ極限展開の閉包所属が
ある有限段階以降ずっと成立することを証明する。
`psi_first_normal_sum_limit_dense` と `psi_first_normal_I_limit_dense` はこれを
和と I の可算尾部の極限枝に適用する。尾部 b の `DenseBelow` は明示的な前提であり、
未知の尾部の共終性を仮定なしに証明したという主張ではない。

`RegularDiagonals.lean` では一般の対角列について、添字 r の正規表現と
正の cutoff での構成可能性から、すべての内側・外側の項の正規表現を導く。
有限パラメータの I(n,m) はこの構成可能性を満たすので、自然数 n,m すべてについて
`revised_finite_parameters_diagonal_fundamentalSequence` が利用できる。

## 非可算パラメータへの拡張

`SeededDiagonal.lean` は、開始項 c<r と c,r の開始閉包への所属から対角列を構成する。
これは添字 r がすべての正の cutoff の閉包に属すという従来の仮定を弱める。
`NormalInterpolation.lean` の補間定理で、正規形の下界から正規な開始項を選べる。
任意の順序数の下界に対する補間ではなく、正規形の下界に対する補間である。

- `revised_psi_first_countable_regular_index_fundamentalSequence`：I(p,b) が正則で、p,b が正規形として表せる可算値である場合。親の正規性条件を用いて開始項を実際に構成する。
- `revised_indexTree_diagonal_fundamentalSequence`：可算の正規項を葉として I と加法を有限回組み合わせた正規項の場合。非可算パラメータも扱える。

`IndexTree` はここで証明済みの族を記述する補助述語であり、既存の正規形を
これだけに制限したり、目標全体をこの族へ縮小したりはしない。
非可算の ψ 値をパラメータとして使う一般の場合は残っている。

`psi_normal_parameters_unique` は添字・引数双方の閉包所属を前提とした ψ の一意性を示す。
現行の `IsNormal` に欠けている添字所属条件を、全項で証明済みとして扱わない。

`ClosureCounterexample.lean` の `normal_closure_not_index_hereditary` は、
正規な ψ 項の値からその表示添字の C 所属を無条件には回収できないことを示す。
具体的に β=`psi (I 1 0) 0`、γ=`psi (I 1 0) 1`、κ=`I 0 (succ γ)` とすると、
`psi κ 0 = β` は C(1,ω) に属するが、κ は属さない。
`closureCounter_normalization` と `revised_closureCounter_fundamentalSequence` により、
この表示にも値を保存する正規化と正当な修正基本列があることを証明する。
反例は、基本列の不可能性ではなく、表示添字を無条件に回収する証明方針への反例である。

## 値を保存する添字の書き換え

`psi_index_plateau` は、任意の順序数 a,k,l について
`psi l a ≤ k ≤ l` から `psi k a = psi l a` を導く。
証明は C の seed に関する単調性と最小性を使い、添字の閉包所属を仮定しない。
`ZeroPlateau.lean` はこの一般補題を使い、後続 rank の零引数崩壊と同じ値を持つ
区間全体を既知の正規形と基本列へ帰着する。

`NestedIndex.lean` の `psi_nested_index_eq` は λ=I(r,b) が正則、q<r、a≤t のとき

```
psi (I q (succ (psi λ t))) a = psi λ a
```

を証明する。t に有限性・可算性の条件はない。
`nestedCollapse_replacement_normal` はこの記法項の書き換えの正規性・意味保存、
`nestedCollapse_replacement_smaller` は項サイズの真の減少、
`nestedCollapse_revised_agrees` は修正展開の各値の一致を証明する。
`revised_nested_successor_rank_zero_fundamentalSequence` は、任意の正規 rank r、q≤r、
任意の内側引数 t について零引数の修正基本列の正当性を与える。
全場合を扱う書き換え手続きと一般の基本列の完成は引き続き未完了である。

`NestedNormalization.lean` の `Nested.normalize` は、上の書き換えを部分項の
任意の位置で適用する停止する処理である。`normalize_spec`、`normalize_normal`、
`denote_normalize`、`normalize_idempotent` により、この規則に関する既約性、
正規形・値の保存、冪等性を証明する。別の規則で等しい値になる項をすべて
同一構文にすることまでは主張しない。

## 非可算崩壊値を含む閉包の回収と対角列

λ=I(r+1,0)、β=ψλ0 とする。`SuccessorRankClosure.lean` は次を証明する。

- `C_successor_rank_interval`：β≤x≤λ かつ x∈C(cutoff,seed) なら r∈C(cutoff,seed)。r は RankBounded であり、有限正規項ならこの条件を満たす。
- `successor_rank_small_presentation`：a<I(0,0) かつ ψκb=ψλa（κ は正則添字）なら κ≤λ かつ b=a。
- `C_successor_rank_small_parameters`：同じ a について ψλa の C 所属から r,a の所属を導く。

`successor_rank_below_presentation` と `C_successor_rank_below_parameters` は、
これを a<λ かつ a∈C(a,ψλa) という条件に一般化する。a は非可算でもよい。

これらは表示された κ が C に属すという誤った仮定を使わない。
`CollapseTrees.lean` の `CollapseTree` は、既存の `IndexTree` に加え、
この ψλa を rank の中にも、λ 未満の正規な引数の中にも再帰的に使える族を記述する。
`revised_collapseTree_diagonal_normalFundamentalSequence` は対角崩壊 ψΩt の修正列が
正規形を保存する実順序数の基本列であることを、
`collapseTree_diagonal_cofinality` はその共終数が ω であることを証明する。
親の正規性に対応する閉包条件と t が正則添字であることは明示的な前提である。
これは一般の正規項全体の証明を、この族への制限で置き換えるものではない。

## 後続 rank の添字における全後続引数

`SuccessorRankSequences.lean` は、λ=I(r+1,0) について

```
b₀ = succ (psi λ a)
bₙ₊₁ = I(r, bₙ)
supₙ bₙ = psi λ (succ a)
```

を証明する。r は RankBounded、a は C(a,ψλa) に属す。a は非可算でもよい。
`successor_rank_succ_fundamentalSequence` が狭義増加・親より真に小さいこと・共終性を与える。
`revised_successor_rank_normal_succ_normalFundamentalSequence` は、親が正規な場合、
前者の閉包所属を導いて修正基本列の正規形保存を証明する。
`successor_rank_normal_succ_cofinality` で最小添字長が ω であることも確認する。

`successor_rank_limit_normalFundamentalSequence` は a<λ の正規な極限引数について、
既知の順序数長の正規基本列を ψλ に移す。引数の基本列の存在そのものは前提である。
一方 `revised_successor_rank_bounded_argument_fundamentalSequence` は、
a が最初の対角崩壊以下の正規項である区間全体を、密度の未証明の前提なしで扱う。

## 極限 rank の零引数・後続引数

`LimitRankSequences.lean` は、r が極限かつ RankBounded、λ=I(r,0) の場合、

```
psi λ 0 = sup_{q<r} I(q,0)
psi λ (succ a) = sup_{q<r} I(q,succ(psi λ a))
```

を証明する。後者は a∈C(a,ψλa) を前提とし、a の可算性を要求しない。
r の正規基本列 f を用いれば、それぞれ I(f(i),0)、I(f(i),succ(ψλa)) が
実順序数の共終な基本列になり、正規添字での出力も正規形になる。
最小長の列を引き継ぐ場合は、親の共終数が r の共終数と等しいことも従う。

具体的に Ω=I(0,0) とすると、`uncountable_rank_zero_normalFundamentalSequence` は
ψ(I(Ω,0),0) に対する Ω 長の基本列 i↦I(i,0) を与える。
`uncountable_rank_zero_cofinality` はその共終数が Ω と等しいことを証明する。
`not_dense_uncountable_rank_zero` により、この値を自然数添字の修正列で共終に
近似することはできない。正規値全体への有限展開の到達性とは区別する。

## 証明済みの枝の統合

`SequenceAssembly.lean` の `SequenceTerm` は、加法・I・証明済みの ψ の枝を
繰り返し組み合わせる。I(r,0) の崩壊では r が零・後続・極限のすべてを扱い、
引数も零・後続・添字未満の正規な極限を扱う。既知の対角枝と値の等しい
別表現も含む。固定される rank や加法の左辺には必要な正規性だけを要求する。

`SequenceTerm.minimal_normal_sequence` は、この族の任意の極限項について、
実際の共終数を添字長とする正規基本列の存在と、添字長の正規表現を証明する。
`minimalSequence` は証明された列を選ぶ順序数関数であり、`minimalStepTerm` は
その正規添字に対応する正規項を選ぶ。正規性・値の一致・親より小さいこと・
狭義増加をそれぞれ証明する。順序数全体での共終性は `minimalSequence_spec` が与える。
自然数長の場合、`SequenceTerm.revised_fundamentalSequence` が従来の修正展開へ戻す。

未処理の ψ の枝を仮定として済ませたり、`IsNormal` の定義をこの族に縮小したりしていない。
一般の I(r,succ b) の崩壊添字や、添字以上の極限引数などが残る。

任意の正規な親について `NormalFundamentalSequence` を構成する定理は未完了である。
この仕様の導入や任意順序数の `intrinsicSequence_spec` を、その正規形保存の証明と
読み替えてはならない。

## 作業の順序

全体の到達性を一般の共終性の証明と取り違えない。
一般の共終性・必要な非可算添字の扱いを仕上げた後、Term3 との対応を証明付きシートに反映する。
