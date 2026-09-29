# Denis の閉包意味論と基本列規則10.5の不整合

この文書の順序数に関する主張は、`SequenceObstruction.lean` と
`Source2019.lean` で Lean による証明を与えている。
到達不能基数の存在は、従来どおり明示的な `Supply` 仮定である。

## 対象とした原文

- [著者の Source、Section VI](https://sites.google.com/site/travelingtotheinfinity/my-system-of-number-names/source)：C の閉包定義と ψ の最小値定義。
- [2019年版、Section 2](https://sites.google.com/site/travelingtotheinfinity/the-collapsing-functions-using-math-alpha-beta-math--weakly-inaccessible-cardinals)：OT 条件6、比較規則9、基本列規則10.5、末尾の * 操作。

2017年の画像そのものは今回のブラウザー取得に失敗したため、閉包の定義は
著者がテキストで掲載している Source の Section VI と照合した。
画像に別の条件があるかどうかは未確認である。

## 反例

ρ = I(1,0)、β = ψρ(0)、κ = I(0,β+1)、α = ψκ(0) と置く。
すべて有限の記法項で表せる。

Lean で次を証明した。

1. β < κ < ρ。κ は許された正則添字である。
2. α = β。
3. β と α は意味論上の正規形条件と2019年版の OT 条件を満たす。
4. 2019年版規則10.5は α[1] = β を返す。
5. 2019年版比較規則は β ⊲ α を返す。

したがって、この基本列の第1項は親の順序数と等しく、降下性が成立しない。
また原文に記された構文的比較と順序数の大小の一致も、この例で破れる。
構文的順序それ自体が非整礎であることまでは主張していない。

## 等式 α = β の証明の内容

β は C(0,β)∩ρ ⊆ β を満たす。κ<ρ なので、同じ β は
C(0,β)∩κ ⊆ β も満たす。最小性から α≤β である。

一方、x₀=0、xₙ₊₁=I(0,xₙ) とする。`IndexIteration.lean` で
β=supₙ xₙ を証明した。この反復列の全項は C(0,α) に入り、
xₙ<β<κ だから、α の閉包条件により xₙ<α。
上限を取ると β≤α。よって α=β。

さらに I(0,β)=β も証明してある。

## * 操作を省略していないこと

β=ψρ(0) なので e(β)=e(ρ)=1。一方、κ の rank は0である。
したがって2019年版の * 操作は κ*=β を返す。
規則10.5の α[1]=κ*⊗1 は β になる。

著者の Source に記載された I(0,β) を直接使う版でも、I(0,β)=β なので
同じ不一致が生じる。

## Lean の主要定理

| 内容 | 定理 |
|---|---|
| α=β | `OCF.Denis.obstructionValue_eq_base` |
| I(0,β)=β | `OCF.Denis.obstructionBase_fixedpoint` |
| 有限正規項だが異なる構文が同じ値を持つ | `T.Correspondence.Denis.obstruction_normal_distinct_same_value` |
| 2019年版 OT 所属 | `T.Correspondence.Denis.Source2019.obstructionTerm_OT` |
| * の計算 | `T.Correspondence.Denis.Source2019.obstruction_star` |
| 規則10.5の第1項と親が等しい | `T.Correspondence.Denis.Source2019.ruleFive_first_equals_parent` |
| 基本列条件への反例 | `T.Correspondence.Denis.Source2019.ruleFive_not_fundamentalSequence` |
| 構文的比較と意味論の不一致 | `T.Correspondence.Denis.Source2019.order_semantics_counterexample` |

`Source2019.lt` は原文の比較規則を有限項上で計算する。
和は二分木による右結合表現で、正規な和の先頭項を使う。
不適切な ψ 添字を与えた場合のフォールバックは反例の計算では使わない。

## 再検証

```powershell
$env:ELAN_HOME = 'C:/Users/Owner/.elan'
lake build Multi.term3.Denis.Source2019
lake env lean ProofAuditTerm3Denis.lean
```

既存の意味論を修正せず、その意味論への反例として保存している。
定義の修正を採用する場合は、旧定義へのこの反例と修正後の証明を区別する必要がある。
