# Term3 と Denis の OCF の対応

比較対象は Denis Maksudov の *Fundamental sequences for the functions
collapsing α-weakly inaccessible cardinals* の定義である。

- [2019年の記法・基本列規則](https://sites.google.com/site/travelingtotheinfinity/the-collapsing-functions-using-math-alpha-beta-math--weakly-inaccessible-cardinals)
- [順序数上の閉包定義を含む著者の Source、Section VI](https://sites.google.com/site/travelingtotheinfinity/my-system-of-number-names/source)

## 検証で判明した不整合

**原文の閉包による意味論と2019年版の基本列規則10.5は、そのままでは両立しない。**
`SequenceObstruction.lean` と `Source2019.lean` に Lean で確認した反例がある。
ρ=`I(1,0)`、β=`psi ρ 0`、κ=`I(0,β+1)`、α=`psi κ 0` と置くと、
**α=β** だが、2019年版規則10.5は **α[1]=β** を指定する。
したがって第1項が親より小さいという基本列の条件を満たさない。
原文の `*` による正規化も反例に含めて確認している。

反例の2項は、実装した意味論上の正規形条件と、2019年版の構文的 OT 条件の
両方を満たす。2019年版の比較規則は β⊲α を返すため、原文の閉包意味論との
順序保存も破れる。**これは2019年版の構文的順序単独の非整礎性を示すものではない。**

詳細は [COUNTEREXAMPLE.md](COUNTEREXAMPLE.md)。定義を変更してこの反例を隠してはならない。
原定義のまま「基本列全体が正当」とする証明は完成できない。

## 利用者の指定に従う修正方針と現在の証明範囲

**OCF の閉包定義と ψ は維持し、基本列側を修正する。**
元の定義と反例は残したまま、`Covering.lean` 以降で置換用の展開を構成している。

- `Covering.lean` はすべての有限項を列挙し、親より小さい正規項の値の有限最大値を取る。
- `RevisedSequences.lean` は後続の場合に前者を返し、極限では値が増加する最初の列挙段階を順次選ぶ。
- `RevisedNormal.lean` は正規形の出力、同じ順序数を表す構文の代表選択、代表上の整列順序を証明する。OCF の値や表現される順序数の範囲は変えない。
- `follow_exists_iff_le` は、ある親から有限回の展開で到達する値が、正確にその親以下の正規形の値全体であることを示す。
- `all_normal_ordinals_reachable` は rank 塔の根の族から正規形全体を覆うことを示す。有限部分や特定の枝だけの定理ではない。
- `NormalSuccessors.lean` は正規形の後続・前者への閉性を証明する。修正展開は後続順序数で実際の前者を返し、すべての実際の極限順序数で狭義増加する。

**未完了の点:** 正規形の集合内での共終性と、元の順序数そのものでの共終性を区別する。
後者は `DenseBelow` と同値であり、一般のすべての対象についてはまだ証明していない。
`RevisedCofinality.lean` では ω、`psi (I 0 0) (I 0 0)`、
`psi (I 1 0) 0`、`psi (I 0 0) (I 1 0)`、および上記反例の親について証明済みである。
非可算正則基数では `DenseBelow` が成立しないこと自体を証明しており、
自然数添字の置換展開をそのまま順序数としての基本列だと扱ってはならない。
正則基数の恒等基本列は既存の順序数添字の定理で扱い、全場合の統合は継続課題とする。

詳細な仕様と定理一覧は [REVISED_SEQUENCES.md](REVISED_SEQUENCES.md)。

## 現時点の形式化

`Cardinals.lean` は実際の順序数 `OCF.Ordinal` 上で有限順序数、ω、
非可算正則性、rank-弱到達不能性、列挙関数 `I` を定義する。
`Supply` は各 rank の弱到達不能基数が非有界に存在するという明示的仮定である。
Lean の `axiom` 宣言によってその存在を追加してはいない。
列挙関数の零・後続・極限の場合の定義式も証明済みである。

`Collapse.lean` は閉包 `C(α,β)` を順序数上の帰納的述語で定義し、
零、β未満の順序数、加法、`I`、α未満の引数での崩壊について閉じる。
`C_least` はこの閉包の最小性を示す。`psi` は順序数の整礎再帰で構成する。

`Small.lean` は正則性から有限式全体の小ささを証明する。
`WellDefined.lean` は閉包の上界を可算回反復し、その上限を使って
一般の正則添字 κ とすべての引数 α に対する **`psi κ α < κ`** を証明する。
`psi_spec` と `psi_exists_unique` により、許された添字では著者の
厳密な最小値定義が存在し、一意であることが証明済みである。
構成時の境界値 κ への退化は、この定理で排除される。
これらは明示的な `Supply` 仮定の下での定理であり、基数の存在自体の証明ではない。
`psi_first_zero`・`psi_first_one` とそれぞれの strict 補題により、
κ=`I(0,0)`、α=0,1 では実際の崩壊値が 1,ω であることが証明済みである。

`../Term3Correspondence.lean` は Term3 の構文的計算と OT 所属を証明する。
`Denis.Term` は別途用意した記法構文であり、OCF 自体の代用品ではない。
`../Term3Denis.lean` がこの構文を実際の `I` と `psi` に解釈する。

全自然数 n と ω について、`read_ofNat`、`read_omega`、
`read_fund_ofNat_succ`、`read_fund_omega` が実際の順序数との対応を与える。
`epsilon_sequence_shift_ordinal` は基本列の1項ずれの等式を証明する。
さらに `EpsilonSequence.lean` は、ψ の反復列の上限が実際の
`psi (I 0 0) (I 0 0)` と一致することを証明する。
`epsilon_fundamentalSequence` と `Denis.epsilonSeq_fundamentalSequence` により、
Term3 の列と Denis の列の降下性・狭義増加性・共終性が証明済みである。
別途定義された ω 冪の最初の不動点 ε₀との同定はまだ証明していない。

`Sequences.lean` は基本列の上記3性質を `FundamentalSequence` として定義する。
加法、`I` の可算極限、正規形の条件を明示した ψ の可算極限について、
この性質を保つことを証明する。正則基数の恒等基本列と、
より短い順序数を添字とする列が共終にはなれないことも証明済みである。
`psi_fundamentalSequence` の引数・添字の閉包所属仮定は、一般の場合には残っている。

`Cofinality.lean` は、実際の極限順序数に共終な写像を持つ最小の添字長を
`cofinality` と定義する。最小性を利用した整礎再帰によって、その長さで
狭義増加する `intrinsicSequence` を構成する。可算基本列が存在すれば共終数は ω、
非可算正則基数の共終数は自身になる。共終数の冪等性と、ω より大きい共終数の
正則性も証明済みである。ただし、この一般構成だけでは値の有限正規形表現は得られない。

`TransfiniteRules.lean` は加法・I・ψの連続性と基本列保存則を順序数添字に拡張する。
任意の狭義増加共終列について親と添字長の共終数が一致するため、
共終数を添字長にして適用したこれらの保存則は最小の長さを保つ。
ψ の閉包所属条件は依然として明示的な仮定である。

`NormalAddition.lean` の `addTerm` は正規項の順序数和を正規化し、
`addTerm_normal` と `denote_addTerm` が正規性と意味の保存を証明する。
既知の `DenseBelow` はこの加法と I の極限操作で保存される。

`RevisedDomains.lean` は、すべての順序数添字で基本列の3性質を満たし、
正規形として表せる添字では出力も正規形となる、という共通の仕様を定義する。
修正した可算列と正則基数の恒等列はこれを満たし、加法・I と条件付きの ψ が保存する。
これは一般の親で仕様を満たす枝を構成し終えたことを意味しない。

`DiagonalSequence.lean` は、最初の弱到達不能基数 κ=`I(1,0)` に対する
Denis の列 `γ₀=1, γₙ₊₁=psi κ γₙ, αₙ=psi (I 0 0) γₙ` が
`psi (I 0 0) κ` の基本列であることを証明する。
`Denis.collapseISeq_fundamentalSequence` が記法構文の解釈との一致を与える。

`../Term3DenisNormal.lean` は Denis の正規形条件を順序数の意味論で定義し、
上の2つの対角的崩壊とその基本列の各項が正規形であることを証明する。
ここでの `Denis.IsNormal` は、Term3 自身の `T.isNF` とは別の述語である。

`IndexLaws.lean`、`IndexIteration.lean`、`RankBound.lean` は、
下位 rank に対する閉包、正規な I 表現のパラメータの一意性、
有限正規項の rank 上界を証明する。これにより、任意の有限正規 rank 項 r に対する
規則10.7（`psi (I (r+1) 0) 0` の I(r,·) 反復列）の正当性と正規形保存は証明済みである。

`../Term3DenisOrder.lean` は、解釈された順序数の集合の整列性と、
正規項に引き戻した順序の整礎性を証明する。
ただし構文の異なる正規項が同じ値を持つ反例があるため、これを正規構文の
一意性や2019年版比較規則の正当性の証明と読み替えてはならない。

`collapseI_sequence_zero_ne_ordinal` は、直接の構文読み替えでは
最初の弱到達不能基数を使う枝の第0項が 1 と ω に分かれることを示す。
これはこの読み替えによる点ごとの一致への反例であり、
別の写像や共終的な再添字づけの不可能性は主張していない。

## 記号

- `one = P Z Z Z Z`
- `exp a = P Z Z a Z`
- `card a = P Z a Z Z`
- `uncountable = card one`
- `inaccessible = P one Z Z Z`
- `epsilon = exp uncountable`
- `collapseI = exp inaccessible`
- `cardFixed = card inaccessible`

これらは Term3 項の名前である。名前だけで順序数同定を仮定しない。
`uncountable`・`inaccessible`・`cardFixed` は内部パラメータであり、
それぞれ OT に属さないことも証明している。

## 検証

```powershell
$env:ELAN_HOME = 'C:/Users/Owner/.elan'
lake build Multi.term3.Denis.RevisedDomains
lake env lean ProofAuditTerm3Denis.lean
```

項の計算証明では propext・Quot.sound のみを許可する。
OCF の意味論では利用者の許可に従い Classical.choice も許可する。
監査は `sorryAx` とそれ以外の公理を拒否する。
既存の未完成の `Term3.lean` は import しない。

## 継続する課題

1. 元の OCF を維持した修正展開について、実際の順序数での共終性を一般の可算対象で証明する。正規形集合内の共終性や到達性の定理で代用しない。
2. 非可算添字を必要とする場合を統合し、順序数としての基本列全体を完成させる。
3. 新しい枝を構成する際には `cofinality_eq_of_minimal_length` を適用し、最小添字長を持つことまで確認する。共終数そのものと一般の長さ比較定理は証明済みである。
4. ε₀以降の同定を証明し、直接読み替えが合わない高階の枝の写像を修正する。
5. Term3 の正規形全体での順序保存、OT 所属、fund 互換性を証明する。
6. 証明が通った対応だけを表に追加し、式を割り当てただけの項を同定済みにしない。

研究目標全体は未完了である。有限部分だけで完了とはしない。
