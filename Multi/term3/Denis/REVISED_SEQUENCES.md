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
添字長が ω の場合には全添字が有限順序数なので、これは各項が正規形であることを意味する。
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

## 後続添字の零引数

`SuccessorIndexSequences.lean` は κ=I(r,succ b)、ρ=I(r,b) とし、
κ∈C(0,ψκ0) の場合の基本列を証明する。

| rank | ψκ0 に共終な列 | 定理 |
|---|---|---|
| r=0 | ρ の有限和 | `rank_zero_successor_index_zero_fundamentalSequence` |
| r=q+1 | succ ρ から I(q,·) を反復 | `successor_rank_successor_index_zero_fundamentalSequence` |
| 極限 r | r の基本列 f を I(f(i),succ ρ) に写す | `limit_rank_successor_index_zero_transfiniteFundamentalSequence` |

パラメータが正規形で表せる場合、前二者は `DenseBelow` を満たし、
極限 rank の列は `limit_rank_successor_index_zero_normalFundamentalSequence` により
r の基本列の正規形保存と最小長を引き継ぐ。
`hasNormalSequence_successor_index_zero` がこれらの枝を統合する。

添字の閉包所属は `C_successor_index_iff` により ρ<ψκa と同値である。
`C_successor_index_of_small_parameters` は r,b<I(0,0) のとき、任意の引数 a で
この所属を導く。正規な引数という条件だけで添字の所属を仮定してはいない。
所属がない場合は `psi_successor_index_plateau_of_not_mem` により ψρa=ψκa となる。
ただし b が極限なら ρ は正則とは限らず、この等式だけで基本列の正当性は結論しない。

## 後続添字の後続引数と添字所属の判定

`SuccessorIndexArguments.lean` は同じ κ=I(r,succ b)、ρ=I(r,b) について、
p=ψκa、u=ρ+p と置く。a∈C(a,p)、κ∈C(succ a,ψκ(succ a)) を前提として、
次の列の上限が ψκ(succ a) に一致することを証明する。

| rank | 共終な列 | 定理 |
|---|---|---|
| r=0 | u の有限和 | `rank_zero_successor_index_succ_fundamentalSequence` |
| r=q+1 | succ u から I(q,·) を反復 | `successor_rank_successor_index_succ_fundamentalSequence` |
| 極限 r | r の基本列 f を I(f(i),succ u) に写す | `limit_rank_successor_index_succ_transfiniteFundamentalSequence` |

a の閉包所属は親の正規性から導かれる。κ の所属は親でのみ要求し、
零引数や直前の崩壊での所属を仮定しない。ρ を含む開始値を使うことで、
直前の ψ 値が ρ 以下にとどまる場合も扱う。
`C_succ_successor_index_bound` が閉包全体の上界を証明し、
`successorIndexBase_mem` が開始値を親の閉包内で構成する。

パラメータが正規形で表せれば列の各値も正規形で表せる。
`hasNormalSequence_successor_index_succ` が最小添字長まで統合し、
r が零・後続なら ω、極限なら r の共終数を引き継ぐ。
引数 a に可算性や κ 未満という制限はない。

`C_successor_index_iff_parameter` は r が RankBounded のとき、
κ∈C(a,ψκa) と b<ψκa の同値を証明する。有限正規項の rank はこの条件を満たす。
したがって b<Ω または b≤r の場合は、任意の引数で添字所属を導ける。
`SequenceTerm.successorIndexSmallParameter` と
`SequenceTerm.successorIndexParameterLeRank` は、零・後続・κ 未満の極限引数の
統合定理からこの所属仮定を除く。極限の場合の引数・rank の列は既知であることを要求する。

`uncountable_rank_successor_index_zero_normalFundamentalSequence` は
ψ(I(Ω,1),0) に対して i↦I(i,succ(I(Ω,0))) という Ω 長の正規基本列を与え、
`uncountable_rank_successor_index_zero_cofinality` は最小長が Ω と等しいことを証明する。

## 可算共終数の極限引数での所属条件の導出

`NormalLimitTransfer.lean` は任意の正則添字 κ と a<κ について、
正規形の可算基本列 f が a に共終であり、a と κ が親の閉包に属す場合を扱う。
`psi_limit_eventual_index_mem` は C の有限性と ψ の連続性により、
ある N 以降では κ∈C(f(n+N),ψκ(f(n+N))) が成立することを導く。
`psi_normal_limit_shift_fundamentalSequence` は、この尾部の ψ 像の3性質を証明する。

`psi_normal_countable_limit_dense` は正規形保存を加え、
`hasNormalSequence_countable_limit_collapse` が既知の最小長 ω の正規基本列を引き継ぐ。
零引数での添字所属を仮定する必要はない。非可算長の列では、
尾部を取るだけで正規添字に対する出力の正規形保存が従うとはしていない。

## 順序数長の正規な尾部

`TransfiniteTails.lean` の `NormalFundamentalSequence.shift` は、
長さ λ が加法的主項であり、c<λ が正規形で表せるとき、
i↦f(c+i) が同じ長さの正規基本列であると証明する。
`cofinality_addPrincipal` により、最小長を用いる場合は長さの条件が自動的に満たされる。
正規添字 i に対する c+i の正規表現は、既存の順序数加法の正規化から構成する。

`psi_normal_limit_tail_normalFundamentalSequence` は a<κ の正規な親について、
正規な開始位置 c での添字所属から、すべての尾部の添字所属を導く。
`successor_index_limit_tail_normalFundamentalSequence` は κ=I(r,succ b)、b<λ の場合に
c=succ b を明示的に使い、この開始位置での所属も証明する。
すべての狭義増加基本列に i≤f(i) が成立することと、親の引数の正規性を用いる。
κ が零引数や親の閉包に属すことを追加の前提にはしていない。

`hasNormalSequence_successor_index_limit_tail` と `SequenceTerm.successorIndexLimitTail` は、
既知の a の正規基本列を、b<cf(a)、a<κ の場合に ψκa へ移す。
最小添字長は cf(a) のままであり、非可算共終数も扱える。

## 零引数の一般的な添字の帰着

`ZeroIndexNormalization.lean` の `ZeroIndex.exists_normal_index` は、
任意の正規な正則添字項 k について、I(r,b) 型の部分項 j を選び、
ψ(k,0)=ψ(j,0) と j∈C(0,ψ(j,0)) を同時に証明する。
元の k の閉包所属は要求しない。

`ZeroIndex.collapse_support` は、ψ(k,0) 以上かつ k 未満の正規項に、
同じ区間に値を持つ ψ 部分項が存在すると示す。
零引数の C では加法と I だけからこの区間に出られないことを利用する。
`psi_zero_eq_of_collapse_between` により、その部分項の添字へ帰着しても零崩壊値は変わらない。
帰着は項サイズを真に減らすため、順序数としての添字が増える場合でも停止する。

`normalIndexPair` は証明された I 項のパラメータを選ぶ Lean の定義であり、
`normalIndexPair_spec` が部分項性・正規性・正則性・閉包所属・値の一致を与える。
`normalIndexPair_rank_smaller` は rank 項が元の添字項より真に小さいことを保証する。
一般の非零引数に同じ帰着を適用できるとは主張していない。

`hasNormalSequence_zero_collapse_induction` は、この帰着先の rank についての
構造的帰納仮定を使い、零引数の正規基本列と最小添字長を構成する。
すべての正規な正則添字についての零引数の帰納段階を扱うが、
任意の rank 自身の基本列の存在までこの定理だけで得るわけではない。

## 任意の引数での閉包所属を満たす表示への帰着

`CollapseNormalization.lean` は、正規な ψκa で κ∉C(a,ψκa) の場合、
より小さい正規 ψ 項で同じ値を表せることを `smaller_of_index_not_mem` で証明する。
添字の中から、ψκa≤ψλb<κ となる ψ 部分項を取り出す。
b≤a なら ψκa=ψλb、a≤b なら ψκa=ψλa として帰着する。
前者では引数も変わるため、零引数用の添字の書き換えだけの一般化ではない。

`psi_not_uncountableRegular` は ψ の値自身は非可算正則にならないことを、
添字に関する冪等性と `psi_lt` から証明する。
これと正規な和の性質により、正則添字を表す正規項は構文上も I 項である。

`exists_proper` は項サイズによる整礎帰納法で、すべての正規な ψ 項を、
添字と引数がともに自身の閉包に属する正規表示 ψ(I(r,b),a) へ帰着する。
`normalize` はこの存在定理に基づく非計算的な定義である。
`normalize_spec`、`normalize_normal`、`normalize_idempotent` は、
閉包所属・値・サイズ上界・正規性・冪等性を保証する。
`parameters_unique` はこの表示同士の rank・I の引数・ψ の引数の順序数値の一意性を示す。
部分項の異なる綴りまで同一構文になるとは主張しない。

`hasNormalSequence_collapse_of_index_not_mem` は添字所属の欠ける枝を、
`hasNormalSequence_nonlimit_collapse_induction` は零・後続引数の枝全体を、
小さい正規項への帰納仮定から処理する。どちらも親の値や引数の可算性を要求しない。
`properLimitStep_iff_all_normal` は、残る極限枝の帰納段階 `ProperLimitStep` と、
全正規項での最小長の正規基本列の存在が同値であると証明する。
これは残る課題の形式的な帰着であり、`ProperLimitStep` 自体の証明ではない。
この命題を公理や暗黙のインスタンスとして使ってはいない。

## 添字未満の極限引数での一般の共終数

`ProperLimitCofinality.lean` の `psi_limit_index_mem_at_stage` は、
任意の順序数長の基本列について、親での添字所属がある一つの段階で成立すると示す。
`psi_normal_limit_transfinite_tail` は、長さが加法的主項ならその段階からの尾部を
ψ に写して実際の順序数の基本列を得る。a<κ と親の閉包所属を前提とする。

`psi_proper_limit_isLimit` と `psi_proper_limit_cofinality` により、a が極限かつ a<κ、
κ,a∈C(a,ψκa) なら ψκa も極限であり、cf(ψκa)=cf(a) となる。
ここでの尾部の開始位置には正規表現を要求していない。
この意味論上の等式を、非可算長の列の一般の正規形保存の証明と読み替えない。

## 崩壊添字以上の正則引数

`RegularArgumentSequences.lean` は κ≤R、κ,R が正則添字、
κ,R∈C(R,ψκR) の場合に、

```
f₀ = 0
fₙ₊₁ = ψR(fₙ)
gₙ = ψκ(fₙ)
```

を使う。`regularArgumentSeq_sup` は sup g=ψκR を証明する。
`regularArgument_tail` は有限の N を構成し、gₙ₊N の基本列の3性質と
引数の閉包所属を証明する。必要な N は親の閉包所属から導かれ、
任意の正規開始項の存在を追加の仮定にしていない。
`proper_regular_argument_dense` が各項の正規表現を保証する。
`regularArgument_cofinality` により最小添字長は ω である。
κ=R も含み、外側の添字を最初の正則添字 Ω に限定しない。

## 任意の正則添字と可算尾部を持つ複合引数

`CompositeLimitSequences.lean` の `proper_composite_countable_dense` は、
引数を op(b) とし、op が固定パラメータと可変パラメータの閉包所属・
正規表現を保存する場合の共通の補題である。
固定パラメータの親での所属と b<ψκ(op(b)) から、
有限の開始位置以降で op(f(n)) の正規な閉包所属を得る。
添字 κ の所属も親での所属から導き、共終な ψ 像を構成する。

和 p+b と I(r,b) について、b<κ、親の正規性と添字所属から必要な条件を導ける。
b の共終数が ω で正規基本列が既知なら、引数全体が κ 以上でも適用できる。
`C_normal_sum_head` は主項の繰り返しを許す正規な和から先頭項の所属を回収し、
和の尾部全体が先頭の主項より小さいという追加条件を不要にする。
`hasNormalSequence_sum_argument` と `hasNormalSequence_I_argument` が
尾部の既知の列を最小長の正規基本列へ統合する。

## 正規形で表せる補間段階

`NormalStageInterpolation.lean` の `normal_limit_collapse_interpolation` は、
正則添字 κ、極限 a、正規項の値 x<ψκa に対して、
正規形で表せる c<a で x<ψκc となるものを構成する。
x は有限正規項で表せる値に限定される。任意の順序数 x についての主張ではない。
ψ 部分項の添字が自身の閉包に属さない場合には、
`smaller_of_index_not_mem` の値と正規性を保つ帰着を使う。

`proper_index_mem_at_represented_stage` は、親の添字所属から
κ∈C(c,ψκc) となる正規な c<a の存在を証明する。
`proper_regular_below_normalFundamentalSequence` は、a=R が非可算正則、R<κ のとき、
恒等列の正規な尾部 c+i に ψκ を適用して R 長の正規基本列を得る。
既存の共終数の等式により、この長さは最小である。

`hasNormalSequence_proper_regular_argument` は、この場合と κ≤R の対角列を統合する。
親の添字所属を満たす非可算正則引数はすべて扱う。
一般の非可算長の基本列 f では、正規な c<a があっても
c<f(i) を満たす正規な添字 i を選ぶ問題が残り、この補間だけで解決したとはしない。

## 正規な添字でも共終になる基本列

`IndexStageInterpolation.lean` の `normal_limit_index_interpolation` は、
正規形で表せる rank r と極限 a について、正規値 x<I(r,a) を
正規形で表せる c<a における I(r,c) で上回れることを証明する。
`NormalSequenceCoverage.lean` の `normal_suffix_represented` は、
正規項の値 x=p+y なら y も正規形で表せることを証明する。
p 自身の正規表現は要求しない。これから和の極限でも同様の補間を得る。

`CoveringFundamentalSequence` は `NormalFundamentalSequence` の条件に、

```
x が正規形で表せる ∧ x<a
  → ∃ i, i が正規形で表せる ∧ i<length ∧ x<f(i)
```

を加えた仕様である。出力の正規性だけからこの条件を仮定していない。
すべての ω 長の正規基本列と正則基数の恒等列でこの条件を証明した。
加法・I・ψ の極限操作と、正規な開始位置での尾部もこの性質を保存する。
ψ の保存則では、意味論上の基本列に必要な添字・引数の閉包条件は維持する。

`proper_limit_below_coveringFundamentalSequence` は、正規な親 ψκa、a<κ、
親での添字所属、引数のこの強い基本列から、正規な開始添字を導き、
ψκa に同じ長さの強い基本列を与える。親から正規な段階 d<a を得た後、
追加の共終性で d<f(c) となる正規な添字 c を選ぶ。
長さが加法的主項であることを仮定し、共終数を長さとする場合には自動的に成立する。
非可算長にも適用でき、添字パラメータが cf(a) 未満という制限は不要である。

`HasCoveringSequence` はこの強い列の最小長と、その長さの正規表現を要求する。
`hasCoveringSequence_proper_limit_below` は引数のこの帰納条件を親へ移す。
`CoveringSequenceTerm` は、既知の可算共終数の枝、正則基数、正則引数の崩壊、
加法・I・添字未満の極限崩壊の入れ子を統合し、各項で強い条件が成立すると証明する。
これはすべての `SequenceTerm` や `IsNormal` を覆うとの主張ではない。
特に極限 rank の零・後続崩壊などで強い条件を引き継ぐ証明は、引き続き必要である。
弱い仕様から選んだ既存の `minimalSequence` に、この追加条件を自動的には適用しない。

## 証明済みの枝の統合

`SequenceAssembly.lean` の `SequenceTerm` は、加法・I・証明済みの ψ の枝を
繰り返し組み合わせる。I(r,0) の崩壊では r が零・後続・極限のすべてを扱い、
引数も零・後続・添字未満の正規な極限を扱う。既知の対角枝と値の等しい
別表現も含む。`successorIndexZero` と `successorIndexSucc` は親の閉包に添字が属す
I(r,succ b) の零・後続引数を加える。`successorIndex` は零引数での添字所属から
添字未満の極限引数も扱う。`countableLimit` は親でのみ添字所属を要求する
可算共終数の極限枝である。極限 rank を扱う構成では rank 自身の基本列も前提とする。
それ以外の固定パラメータや加法の左辺には必要な正規性だけを要求する。
`zeroCollapse` は添字内の I 部分項の rank についての列を受け取り、
元の添字の閉包所属を要求せずに零引数を処理する。
`SequenceTerm.normalizedCollapse` は、閉包所属を満たす表示で証明した列を元の項へ移す。
`regularArgument` は親の添字所属を満たすすべての非可算正則引数を扱う。
`countableSumArgument` と `countableIndexArgument` は、添字未満で共終数 ω の
既知の尾部から複合引数の枝を構成する。

`SequenceTerm.minimal_normal_sequence` は、この族の任意の極限項について、
実際の共終数を添字長とする正規基本列の存在と、添字長の正規表現を証明する。
`minimalSequence` は証明された列を選ぶ順序数関数であり、`minimalStepTerm` は
その正規添字に対応する正規項を選ぶ。正規性・値の一致・親より小さいこと・
狭義増加をそれぞれ証明する。順序数全体での共終性は `minimalSequence_spec` が与える。
共終数が ω の場合、`SequenceTerm.revised_fundamentalSequence` が ω 長（自然数添字）の従来の修正展開へ戻す。

未処理の ψ の枝を仮定として済ませたり、`IsNormal` の定義をこの族に縮小したりしていない。
添字所属の欠ける表示、零・後続引数、非可算正則引数の帰納段階は処理済みである。
`properRemainingLimitStep_iff_all_normal` は、全体の定理を非可算正則ではない
極限引数の帰納段階 `ProperRemainingLimitStep` に帰着する。
正規な添字での共終性を持つ列では、添字未満の極限枝の尾部選択は処理済みである。
この強い帰納条件を残る枝にも証明することや、添字以上の残る極限引数などが未完了である。
この帰着先の命題自体を証明済みとしたり、公理として追加したりしていない。

任意の正規な親について `NormalFundamentalSequence` を構成する定理は未完了である。
この仕様の導入や任意順序数の `intrinsicSequence_spec` を、その正規形保存の証明と
読み替えてはならない。

## 作業の順序

全体の到達性を一般の共終性の証明と取り違えない。
一般の共終性・必要な非可算添字の扱いを仕上げた後、Term3 との対応を証明付きシートに反映する。
