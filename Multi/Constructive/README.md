# `term2.lean` の構成的な整礎性証明

`Multi.term2` は、元の項 `T`、順序、正規形 `isNF`、基本列 `fund`、
`isOT` の定義を保ったまま、整礎性を構成的に証明する。
古典的な順序数への解釈に代えて、Lean の帰納的述語 `Acc` と
基本列による相対的な簡約を用いる。ブラウワー順序数の型は導入していない。

## 証明の構成

1. 正規形の集合を表す述語 `X : T.NF → Prop` に対し、基本列による
   簡約関係 `Step X` を定義する。可算な定義域では自然数を入力に使う。
   定義域が `Ω l` の場合には、`X` に属する `Ω l` 未満の項と、必須の入力
   `Ω (fund l Z)` を使う。既存の `fund` の定義は変更しない。

2. `Stage X a := Acc (Step X) a` とする。
   `Distinguished X` は、各 `a ∈ X` 以下で `X` と `Stage X` が一致する条件である。
   これらの述語のいずれかに含まれる項全体を
   `Universal a := ∃ X, Distinguished X ∧ X a` と定義する。

3. 基本列の相対的共終性を示す。大きな定義域の場合、項の構造に関する帰納法で
   `fund s t ≤ r < fund s (t + 1)` を満たす入力 `t` を得る。
   基本列の交換則と区間に関する補題により、`Stage X r` から `Stage X t` を復元する。
   順序数の最小元の選択は用いない。

4. 相対的共終性から、各 `Distinguished X` 上の元の順序が整礎的であることを示す。
   二つのそのような述語は共通の初期区間で一致するため、`Universal` 自身も
   `Distinguished` となる。従って `Universal` 上で整礎帰納法を使える。

5. `Universal` が全正規形を含むことを示す。まず `Ω a` から `Ω (a + 1)` への
   拡張を、下位の指数での相対的簡約の一致から構成する。次いで指数形成、
   定義域の指数の取り出し、和、主項 `P a b Z` に関する閉包性を証明する。
   崩壊する場合の有限反復は自然数帰納法で扱い、引数の減少には
   `Universal` 上の整礎帰納法を使う。

6. 正規形の構造に関する帰納法で全正規形の所属を得て、元の順序の整礎性を結論する。
   既存の基本列の補題と合わせると `T.OT_is_NF` と `T.OT_is_wellfounded` が従う。

## ファイル

| ファイル | 内容 |
| --- | --- |
| `../Term2Syntax.lean` | 元の項・正規形・基本列の定義と、それらの構成的な補題 |
| `../Term2Consequences.lean` | `OT` の定義と、整礎性を仮定して両方式で使う共通の補題 |
| `Stages.lean` | 相対的簡約と `Distinguished` に関する一般論 |
| `Term2Stages.lean` | `fund` に対する入力と簡約の定義 |
| `Term2Anchors.lean` | 必須入力と基本列の区間に関する補題 |
| `Term2Commutation.lean` | 極限入力での基本列の交換則 |
| `Term2Inverse.lean` | 基本列の値から入力の到達可能性を復元する補題 |
| `Term2Brackets.lean` | 区間の入力の構成と相対的共終性 |
| `Term2Universal.lean` | 指数形成、定義域の指数、和に関する閉包性 |
| `Term2Closure.lean` | 崩壊を含む主項の閉包性と全正規形の整礎性 |
| `Term2.lean` | 構成的な三定理 `T.Constructive.*` と、従来の名前 `T.*` での参照 |
| `../term2.lean` | `Multi.Constructive.Term2` を読み込む従来の入口 |
| `Term2Audit.lean` | 公理依存とインポートの検査。証明本体からはインポートされない |

古典的な三定理は `../OCF/Term2.lean` の `T.OCF.*` として提供する。
そこで使う順序数への解釈は `../OCF/Term2Interpretation.lean` にある。
いずれも `Multi.term2` のインポートには含まれず、構成的証明からも参照されない。

両方式の定理名は次のとおりで、両モジュールを同時にインポートできる。

| 結論 | 構成的な証明 | 古典的な証明 |
| --- | --- | --- |
| 正規形の整礎性 | `T.Constructive.NF_is_wellfounded` | `T.OCF.NF_is_wellfounded` |
| `OT` の特徴づけ | `T.Constructive.OT_is_NF` | `T.OCF.OT_is_NF` |
| `OT` の整礎性 | `T.Constructive.OT_is_wellfounded` | `T.OCF.OT_is_wellfounded` |

従来の `T.NF_is_wellfounded`、`T.OT_is_NF`、`T.OT_is_wellfounded` は、
それぞれ構成的な証明を参照する。定理の型は変えていない。

## 検証

Lean の指定バージョンはリポジトリの `lean-toolchain` に従う。

```text
lake build Multi.term2 Multi.Constructive.Term2Audit
```

監査では、この証明がインポートするプロジェクト内の全宣言について公理依存を調べ、
`propext` と `Quot.sound` 以外があればエラーにする。
`Multi.OCF` と mathlib のインポートも拒否する。

三つの結論の `#print axioms` の結果はいずれも `[propext, Quot.sound]` である。
証明本体に `sorry`、新しい公理、古典論理の使用、指定された自動化タクティクはない。
