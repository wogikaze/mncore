---
title: TensorLayout
id: 66bc07cd2f103d001ca1d471
created_unix: 1723598799
updated_unix: 1725202918
views: 19
---

# TensorLayout

[.](https://tech.preferred.jp/ja/blog/mn-core-tensor-layout/)MN-Core における[[テンソル]]の[[メモリ配置レイアウト表現]] - Preferred Networks Research & Development

[[strided layout]]
 `shape=(A, B), strides=(a, b)` のようなレイアウトを `(A:a, B:b)`のように書く
<https://gyazo.com/1df6ec018081f42bb86137594f4541a5>
 [[row major]]
<https://gyazo.com/cac919bf7fad5f03f56c11c2161dcde1>


[/ [[1.1 構成.icon]]]
 LMがそれぞれのアドレス空間を持っているためstrided layoutが使えない
 TensorLayoutにする

<https://gyazo.com/a807024c52c5eb303041b04b327c19dd>`((4_PE, 3), (8))`
<https://gyazo.com/2f5d1b291183feb2e02b25bd83f7fc8b>`((12:2), (4_PE, 2:1))`
<https://gyazo.com/7f7e272e9b54ba9f510953457ed1e412>`((3:8, 4_PE), (8:1))`
<https://gyazo.com/6e8c4688133b9b669c9aa774b10b3946>`((2_PE, 6:4), (2_PE, 4:1))`
 <https://gyazo.com/7b32b64fc9fba121601402801b65553c>2通りできてしまう
  `((2_PE:2, 6:4), (2_PE:1, 4:1))`, `((2_PE:1, 6:4), (2_PE:2, 4:1))`

[[パディング]] / [[PadLayout]]
 行数/列数を2や4の倍数にする
 10x7 → 12x7 `((3:7, 4_PE), (7:1))`→`(10,7) / ((3:7, 4_PE), (7:1))`
  → 10x8 `(10,7)/((10:2), (2:1, 4_PE)) `

[[broadcast]]
 行列を分割せずに全てのLMにコピーする
  4つのPEそれぞれのLMに行列全体のコピーを配置する: `((12:8), (8:1))`
   `((12:8), (8:1); B@[[PE]])`とも

複数の階層でのレイアウト
　別々の軸に割り当てる
　1024x512
　 1024 行を 8 行のまとまりごとに 8 つの L1B に、さらにそれでできた 64 行のまとまりごとに 16 個の L2B に分配し、
  512 列について、連続する 4 列は 4 つの PE に分配した上で、32 列のまとまりごとに 16 個の MAB に分配する
 <https://gyazo.com/989139462240e2ade10d38e79ea4986c>`((16_L2B, 8_L1B, 8:8), (16_MAB, 8:1, 4_PE))`
