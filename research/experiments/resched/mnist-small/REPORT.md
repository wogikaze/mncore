# MNIST 小問 5 問の短縮（sumcol-mini / sumrow-mini / onehot-mini / fmul7 / a-b）

## 結果
| 問題 | 記録 | 最良 | 備考 |
|---|---:|---:|---|
| 9.sumrow-mini | 6 | **5** | `9.sumrow-mini/best.vsm`（= c5a.vsm）。`ACCEPTED!! score=5 j=5 m=0 bytes=139`（clean・dirty とも）。記録解とビット一致 |
| 7.sumcol-mini | 4 | 4 | 別解 `s4_l1bm.vsm`（4 語、ACCEPTED） |
| 15.onehot-mini | 7 | 7 | |
| 2.fmul7 | 5 | 5 | |
| 1.a-b | 3 | 3 | |

## 9.sumrow-mini: 6→5
```
imm ui"0x3FC00000" $nowrite
ipassa $llm0v $nowrite; gmwrite $aluf $lx0
fvadd $lm2v4 $aluf $nowrite
gbfn $mauf $nowrite
gmmul $lx $aluf $n0v
```
### 記録解（6 語）
1. `fvpassa $lm0v4` で、サイクル c に行 c の長語 (w0,w1) を MAU に読む。
2. `fvadd $lm2v4 $mauf` で、PE ごとの部分和 (w0+w2, w1+w3) を作る。
3. `gbfn $mauf` で部分和を BF 化する。同じ行の `gmwrite $aluf $lx4` は、zero の出力で行列の行 4–7 を 0 にしている。
4. `imm 0x3FC00000`（BF の 1.0）を出し、同じ行の `gmwrite $aluf $lx0` で行列 A の行 0–3 に部分和を入れる。
5. `gmmul $lx $aluf $ln0` は x = 1.0 なので dst[i] = S_i になる。dst[i] は PE i/2 に入るので、PE0 には (S0,S1)、PE1 には (S2,S3) が入る。
6. `msr $mauf $ln2` で PE1 の (S2,S3) を PE0 の ln2 に移す。

### 効いた変更: 行列と x の役割を入れ替える
- A の行 0 をすべて 1.0（imm → gmwrite）にし、x に BF 化した部分和を入れる。
- gmfma では x[j] が PE j/2 の語 j%2 なので、dst[0] = Σ_j x[j] は「サイクル c に読んだ行 c の 8 個の部分和の和」= S_c になる。dst[0] は PE0 の上位語に入る。
- 単語書き込み `$n0v` を使うと、サイクル c に PE0 の n[c] へ S_c が書かれ、S0..S3 がそのまま並ぶ。msr が要らなくなり、zero 行用の gmwrite も消える。
- 部分和は、ALU の `ipassa $llm0v`（aluf の上位長語が (w0,w1)）と、次の行の MAU `fvadd $lm2v4 $aluf` で作る。imm は L1 の ALU 枠にあり、L1 は LM0 を読まないので衝突しない。
- 積の組み合わせは記録解と同じなので、結果はビット単位で一致する。最大誤差は 8.0e-5 で、記録解と同じである（tight tolerance の testcase `tc_tight.vsm` と `tight.sh` で測った）。

### 4 語にならない理由
- **部分和を作る方式では 5 行が下限になる。** ALU には imm、MAU の片方の入力を読む命令、gbfn の 3 命令が要る。MAU には fvadd、gmwrite、gmmul の 3 命令が要る。
  - fvadd には 2 つの入力が要る。片方はその行の LM0、もう片方は前の行の aluf である（GRF だと 2 行かかる）。
  - imm は LM0 を読む行に置けない（`immediate` と `lm0` が衝突する）。
  - 4 行に入れると、gmmul=L4、gbfn=L3、fvadd=L2、読み出し=L1 となる。imm は L2 か L4 にしか置けない。L2 は fvadd が LM0 を読むので置けず、L4 では gmwrite に間に合わない。
- **部分和を作らない方式は精度で落ちる。** 4 行案 `c4a.vsm`（imm / gbfn+gmwrite / gbfn+gmmul / gmfma で y=mauf）は構造としては動く。
  - しかし 16 個の生データを G の BF で量子化するため、誤差が 1.22e-4 になり、許容の 1e-4 を超えた（pos2 と pos3）。
  - 半分ずつの順序を入れ替えた `c4b` も同じ値になった。各半分の誤差は `p1.vsm` と `p2.vsm` で測った（行 3 の前半だけで 1.28e-4）。
- F（fmfma）なら精度は足りる。ただし 1 パスで PE ごとに 1 語、計 4 値しか処理できないので、行数が増える。
- PE をまたいで足す手段は、行列演算か msr/msl しかない。L1BM の縮約は PE 方向が結合なので、和にならない。

## 7.sumcol-mini: 4 のまま
- 記録解は `fpassa $lm0v` → `fvadd $lm4v $aluf` → `fvadd $lm8v $mauf` → `fvadd $lm12v $mauf $ln0v` の直列 4 段である。単語アクセスで、サイクル c が出力の語 c を担当する。
- 別解として、8.sumcol の手法（`ipassa $peid $t` / nop / `l1bmr4ffadd $llmt0v $llbi` / `l1bmm4 $llbi $lln0v`）も 4 語で ACCEPTED になった（`s4_l1bm.vsm`）。足す順序が違うので、golfcheck ではビット不一致になる。
  - 16x1 の `l1bmm` で受けると `Mismatch of bmode in L1BM turnaround` になるので、受けは l1bmm4 にする必要がある。
- **下限（3 行にならない理由）**
  - 出力 1 語は、同じ PE の異なる 4 番地（行）の和である。浮動小数点の加算は MAU（1 行に 2 項）か L1BM/L2BM の縮約でしかできない。
  - 1 行で読める LM0 は 1 番地だけで、2 つ目を読むと `lm0` と `in_lm0` が衝突する（`s3_twolm0.vsm`）。
  - レーンは固定で、ALU は浮動小数点の加算ができない。したがって MAU の鎖は 1 行に 1 項しか増やせず、3 行では 3 項までになる。
  - L1BM の縮約は MAB 間の和である。MAB ごとに別の行を読ませるには T の設定と待ちで 2 行が要り、そこに縮約と受け取りが加わって 4 行になる。
  - 行列演算は PE 間を混ぜるだけで、行（番地）方向の和にはならない。

## 2.fmul7: 5 のまま
- 記録解は `imm 7.0 $t` のあと、`fvmul` を 4 回（1 回 8 語、計 32 語）行う。
- **下限**
  - 単精度の乗算は MAU だけで、1 行 8 語である（hv は精度が足りない）。よって乗算に 4 行が要る。
  - 定数 7.0（または fvfma(x,8,−x) 用の 8.0）を作るには imm が要る。固定値入力（$msb1 など）に 1 入力命令を 1 回かけても、7.0 や 8.0 は作れない。
  - imm は LM0 を読む行に置けない（`f4_immlm0.vsm`: `immediate` と `lm0` が衝突）。また、定数が出る前の行で MAU は掛け算ができない。よって 1+4=5 行が下限である。

## 1.a-b: 3 のまま
- 記録解は `ipassa $llm0v $llr0v`（A を GRF へ写す。aluf の上位も A）のあと、`fvadd $aluf -$lm16v4` と `fvadd $lr2v4 -$lm18v4` を行う。
- **下限**
  - 単精度の加算は MAU だけで、1 行 8 語である。16 語には 2 行要る。
  - LM1 への書き込みは 1 行に 1 回までである。
  - A と B はどちらも LM0 にあり、1 行で 2 番地は読めない。最初の行の MAU は A と B を同時に受け取れないので、計算の 2 行は 2 行目以降になる。よって 3 行が下限である。

## 15.onehot-mini: 7 のまま
- 記録解は次の流れである。
  - imm/0101 0x3F800008 を r2,r3,r6,r7 に置く（1.0 の素と +8 を兼ねる）。
  - packbit → linc → iadd/$imr1 で、T レジスタに列ベクトル (2p+8h, 2p+8h+1) を作る（サイクルで h が交互に変わる）。
  - L1BM の結合と分配で、(Ti,Ti) を GRF1 に複製する。
  - ixor を 2 回行い、hvpassar/$imr を 2 回行う（1 回 8 語）。
- 試して駄目だった・行き止まりの案
  - **2 長語マスク `$llimr` で 1 回に 16 語を書く案。** 2 長語マスクでは 4 ビットが 4 語に対応するので、半語精度の比較（s 精度、4 フラグ）が 1 回あれば足りる。ただし Ti を 4 つの半語すべてに複製する必要がある。L1BM の分配は語単位なので、シフトと OR に ALU が 2 命令以上かかる。列ベクトル (2p,2p+1,2p+8,2p+9) にも 2 命令以上かかり、合計の ALU 命令数は今より増える。
  - **`sxor $subpeid` で比較する案。** 固定値は s 精度では各半語が p になるが、条件は T==2p+c_k である。`spackbit $subpeid` で 2p は 1 命令で作れるが、Y 側に T XOR c_k の半語複製が要り、同じく命令が足りない。
  - **imm と linc を消す案。** `lnot $msb1` と packbit で (2p,2p+1) は作れる。しかし 1.0 と +8 を作るのに imm が要るので、ALU 命令は 6 個のままである。imm の値を r1 に置いて次の行で読む案は、GRF のハザードで落ちる。
  - **MAU で +8 を作って T に書く案。** 非正規化数の加算に頼ることになり、0x3F800008 を足すと 1.0 側に吸収されてしまう。
- **下限の見立て**
  - ALU 命令は 6 つが直列に並ぶ。列ベクトルの生成に 3 命令（imm/packbit/linc。+8 のずらしを入れると 4 命令）と、i 精度の比較 2 回である。
  - i 精度の比較で独立なフラグは 1 サイクルに 2 ビットしかなく、1 回の書き込みは 8 語なので、書き込みは 2 行要る。
  - 最後の比較の次の行が最後の書き込みになるので、7 行になる。

## ファイル
- `t.py`: 16.onehot/t.py を問題指定式（環境変数 P）にした probe 用の道具
- `9.sumrow-mini/best.vsm` = `c5a.vsm`: 5 語の解（ACCEPTED）
- `9.sumrow-mini/c4a.vsm`, `c4b.vsm`: 4 語の候補。G の量子化で誤差 1.22e-4 となり不合格
- `9.sumrow-mini/p1.vsm`, `p2.vsm`: 半分ずつの G の和の誤差を測る probe
- `9.sumrow-mini/tc_tight.vsm`, `tight.sh`: atol をほぼ 0 にして、位置ごとの誤差を表示する
- `7.sumcol-mini/s4_l1bm.vsm`: L1BM 縮約による 4 語の別解（ACCEPTED）
- `7.sumcol-mini/s3_twolm0.vsm`: 3 語の候補。LM0 を 2 回読むので衝突する
- `2.fmul7/f4_immlm0.vsm`: 4 語の候補。imm と LM0 が衝突する
- 各ディレクトリの `base.vsm`: 記録解のコピー
