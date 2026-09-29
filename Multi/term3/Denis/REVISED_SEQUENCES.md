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

一般の可算対象で `DenseBelow` を示すことは未完了である。
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

任意の正規な親について `NormalFundamentalSequence` を構成する定理は未完了である。
この仕様の導入や任意順序数の `intrinsicSequence_spec` を、その正規形保存の証明と
読み替えてはならない。

## 作業の順序

全体の到達性を一般の共終性の証明と取り違えない。
一般の共終性・必要な非可算添字の扱いを仕上げた後、Term3 との対応を証明付きシートに反映する。
