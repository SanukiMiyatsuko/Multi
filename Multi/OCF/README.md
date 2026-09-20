# `term2` の古典的証明

`Multi.OCF.Term2` をインポートすると、次の三定理を利用できる。

- `T.OCF.NF_is_wellfounded`
- `T.OCF.OT_is_NF`
- `T.OCF.OT_is_wellfounded`

`Term2Interpretation.lean` にある順序数への解釈 `T.denote` とその狭義単調性から、
正規形の整礎性を証明する。残る二定理は `../Term2Consequences.lean` の
共通補題に、この整礎性を渡して得る。

三定理の公理依存はいずれも `[propext, Classical.choice, Quot.sound]` である。
構成的証明のモジュールには依存しない。

```text
lake build Multi.OCF.Term2
```

構成的な版は `../Constructive/Term2.lean` の `T.Constructive.*` にある。
二つの版は同時にインポートできる。
従来の `Multi.term2` と `T.*` の三定理は、構成的な版を提供する。
