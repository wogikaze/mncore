# 半精度行列積と公式エミュレータの差をなくす

`hmmul`/`hmmulr`/`hmfma`/`hmfmar` で、拡張表現（指数フィールド 0、指数は共通指数 − 6）の
要素を含むブロックフロートの行列積が公式エミュレータと食い違っていた。原因は 2 つあり、
どちらも SDM 4.5 が「乗算器出力の詳細」として省略している部分だった。

## 1. 拡張表現の積の丸め

SDM 4.5 は、拡張表現の因子が 1 つ（2 つ）の積を加算前に 6（12）ビット右シフトして丸めると
だけ書いている。`exhaust.py` で 9 ビット仮数の全組み合わせ（262,144 通り × 3 種類）を
`hmmul`（単精度出力、1 項だけ非ゼロ）に流して測った。

- 結果は常に `floor(積 / 2^shift)` か、その +1。
- 行側だけ拡張・ベクトル側だけ拡張の表は同一で、引数の入れ替えにも対称。
- 6 ビットシフトの切り上げは、両仮数の下位 6 ビットと floor の偶奇だけで決まる。
  ただし真の余りが半分未満なら切り上げない一方、半分を超えても切り上げないことがあり、
  最近接偶数丸め（一致 92%）、部分積の列の切り詰め、Booth 符号化、オペランドの事前シフト、
  有効ビット数を限った二重丸めのどれも再現しない。
- 12 ビットシフトは 9 ビット全部に依存する。

そこで測定した表をそのまま実装に持たせた（`make_table.py` →
`viz/core/src/hmul_ext_round.bin`、33,792 バイト。`float::ext_product_round_up`）。
SDK 0.9 のエミュレータでもランダムな 8,640 組が表と一致する。

## 2. y（加数）を揃える格子

`hmfma` の y は、拡張表現でない積の格子（`2^(ca + cb − 2 bias + 2 − 18)`）ではなく、
それより 10 ビット細かい `2^(ca + cb − 2 bias + 2 − 28)` に揃える。`hmmul_diff.py --op hmfma`
の 6,144 出力で、この規則だけが全件一致した（積の格子に揃えると 420 件、揃えないと 5,794 件）。

## 確認

```sh
cd research/experiments/hmmul-rounding
python3 hmmul_diff.py --op hmfma --runs 6 --seed 31          # チャレンジ版エミュレータ
python3 hmmul_diff.py --op hmmulr --runs 5 --seed 124 --sdk  # SDK 0.9（Docker）
```

| 比較 | 結果 |
| --- | --- |
| `hmmul`/`hmmulr`/`hmfma`/`hmfmar`（各 6,144 出力、チャレンジ版） | 0 件の差 |
| `hmmul`/`hmmulr`（各 5,120 出力、SDK 0.9） | 0 件の差 |
| MLSDK の add・softmax・matmul・MLP 順伝播・MLP 学習ステップ（各 3 入力、SDK 0.9、`../mlsdk-diff`） | 0 件の差 |

`viz/core/tests/hmmul_reference.rs` は、エミュレータの `hmfma`/`hmmulr` 出力 1,200 件で回帰を防ぐ。

`--sdk` は SDK 0.9 のツールを `mncore-sdk-minimal:0.9` イメージ内で動かす
（`../mlsdk-diff/sdk_run.sh`、ホストの glibc では動かないため）。イメージは
`github.com/pfnet/mncore` の `sdk/0.9/mncore-sdk-minimal.Dockerfile` から作る。
