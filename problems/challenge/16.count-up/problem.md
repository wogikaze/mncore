---
source_url: https://mncore-challenge.preferred.jp/problem/count_up
slug: count_up
fetched_at: 2026-10-14T00:39:00+00:00
---

# Count Up

- Top: 21 lines / syttrea
- Par: 100 lines

## Problem Statement

\(1\) から \(32768\) までの各整数の `Int` を順に Group \(0\) の DRAM の先頭から書き込んでください。
たとえば `$d0@0` には `Long`（`Int` \(2\) つぶん）として \(1 \times 2^{32} + 2\) が、 `$d100@0` には \(201 \times 2^{32} + 202\) が書かれることになります。
問題に取り組む際には[「階層的メモリ間データ転送・行列演算命令の可視化」](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92L2BM%20concat) が役に立つかもしれません。ぜひご活用ください。
### MV 命令・wait 命令について (2024/8/29 追記)

この問題では DRAM 上に答えを生成することになります。
MN-Core 2 では L2BM, DRAM, PDM それぞれの間の転送には MV 命令（[SDM 3.5「MV命令文」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#section.3.5)）を用います。
実はトップページで配布している judge.zip に含まれる "Hello, world!" を DRAM 上に出力するサンプルプログラムでも MV 命令を使っています。
さて、SDM には、MV 命令は発行後後続の命令と非同期に実行され、転送完了を待ち合わせるには wait 命令（[SDM 3.6.13「wait - PE 命令に MV 命令を待機させる」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.6.13)）を用いる、という旨の記述があります。
MN-Core 2 ボード実機で動かすプログラムについては、特に DRAM アクセスが絡むとリフレッシュ等の影響で転送完了タイミングの保証が困難になるため、MV 命令にはタグ（[SDM 3.2.3「タグ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.2.3)）をつけて適当なタイミングで wait 命令で完了を待つ、という書き方をするのが原則となります。
一方、本コンテストは実機ではなくエミュレータ上で評価されます。
エミュレータはサイクルアキュレートではなく MV 命令の転送が命令発行と同時に完了するという実行モデルになっています。
そのため、今回のコンテストでは wait 命令で MV 命令の完了を待ち合わせる必要はありません。
`mvp/n64` などタグなしの MV 命令を用いても次の行以降で転送結果を利用できます。

## Outputs

* UInt `$d[0:16384]@0`, `/((16384:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/count_up/testcase.vsm)
