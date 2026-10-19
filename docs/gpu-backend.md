# GPU バックエンド

## 実行環境

ホストは WSL2 で、GPU は `/dev/dxg` 経由で見える。
`/dev/nvidia*` は存在しないが、`/usr/lib/wsl/lib/libcuda.so.1` があるので CUDA Driver API は使える。
Linux 用の CUDA ツールキットは入っていない。
NVRTC は PyTorch の CUDA wheel に同梱されている `nvidia/cuda_nvrtc/lib/libnvrtc.so.12` を使う。
`nvcc` は不要。

NVRTC は `--device-int128` を付けるとデバイスコードで `unsigned __int128` を扱える。
これで [float.rs](../viz/core/src/float.rs) の 128 bit の仮数演算をほぼそのまま移植できる。

## f32 vfma のプロトタイプ

- [vfma_kernel.cu](../viz/core/gpu/vfma_kernel.cu) は `Fmt`、`Val`、`decode`、`round_pack`、`mul_exact`、`add_exact`、`align_c`、`vfma` を CUDA に移したもの。
- [vfma_vectors.rs](../viz/core/src/bin/vfma_vectors.rs) はランダムな 100 万組の (a, b, c) と、CPU の `float::vfma` の結果を出力する。
- [check_vfma.py](../viz/core/gpu/check_vfma.py) は NVRTC でコンパイルし、Driver API で実行して全ビットを比較する。

```sh
cd viz/core
cargo run --release --bin vfma_vectors -- 1000000 target/vfma_vectors.bin
python3 gpu/check_vfma.py target/vfma_vectors.bin
```

結果:

- 100 万組で mismatch 0。
- バッチ実行は約 4.6 Gvfma/s。
- 1 行分（4,096 PE × 4 サイクル × 2 レーン = 32,768 vfma）の起動は 7.8〜8.2 µs。
- 3,558 行を同一ストリームに積んで 28 ms。

CPU の `fvfma` は 1 行あたり約 3.8 ms（500 行のマイクロベンチ）なので、GPU の方が 2 桁以上速い。

## まだ必要なもの

- LM/GRF の状態を VRAM に置いたままにする。144 MB。
- ALU、MAU（half/double を含む）、マスク、forwarding、msl/msr、block-float、L1BM/L2BM、行列のカーネル。
- 行間の依存は同一ストリームの順序で保証する。1 行 1 カーネルで足りる見込み。
- mncore-sim への組み込みと、`difftest_prog` 相当のビット一致確認。

## 制約

- 起動オーバーヘッドは 1 行 5〜10 µs。3,558 行で 28〜36 ms なので、全体では支配的にならない。
- f32 の vfma は確認済みだが、half と double、block-float はまだ移植していない。
- GPU の状態を毎行ホストに戻すと PCIe 転送が支配的になる。状態は VRAM に置いたままにする。

## Rust ラッパー

[viz/core/src/gpu.rs](../viz/core/src/gpu.rs) は `libloading` で `libcuda.so.1` と NVRTC を実行時に読み、カーネルのコンパイル、コンテキスト、バッファ、起動を Rust から扱う。
[viz/core/src/bin/gpu_vfma.rs](../viz/core/src/bin/gpu_vfma.rs) は CPU の `float::vfma` と全ビットを比較する。

```sh
cd viz/core
cargo run --release --bin gpu_vfma -- 1000000
```

結果:

- 100 万組で mismatch 0。
- CPU は約 15 Mvfma/s。
- GPU は入出力の 12 MB 転送を含めて約 89 Mvfma/s。

この計測は毎回 4 本のバッファを確保し、入力と出力を PCIe で往復させる。
実際のバックエンドでは状態を VRAM に置いたままにするので、この転送は毎行には入らない。
転送を含めた数値は、状態を毎回ホストと往復させてはいけないことの確認でもある。

## MAU 行の実行

`GpuState` は LM0/LM1/GRF0/GRF1 の 144 MB を VRAM に確保し、初期状態だけ転送する。
`mau_line` カーネルは 1 スレッド 1 PE で、4 サイクル分をすべて読んでから書く。
1 サイクルずつ読み書きすると、同じ行の別サイクルが書いた領域を別サイクルが読む場合に CPU と順序が変わるため。

対応している範囲:

- f32 の FMA、MUL、ADD、PASSA。
- `wl = 2`（2 レーン）。
- LM0/LM1/GRF0/GRF1 の直接アドレス。
- マスク、forwarding、T 間接、base レジスタ、neg/ext/rnd はまだ未対応。

[viz/core/src/bin/gpu_mau.rs](../viz/core/src/bin/gpu_mau.rs) は同じランダム行を CPU と GPU で実行し、4 本のメモリ全体を比較する。

```sh
cd viz/core
cargo run --release --bin gpu_mau -- 3558
```

結果:

- 3,558 行で mismatch 0。
- CPU 5.58 秒、GPU 111 ms（行あたり約 31 µs）。
- 状態の転送は最初の 1 回だけで、行ごとの転送はない。

## VSM の MAU 行

[viz/core/src/bin/gpu_vsm_mau.rs](../viz/core/src/bin/gpu_vsm_mau.rs) は VSM をパースし、f32 MAU 行のオペランドから `MauLine` を組み立てる。
CPU 側は `Sim` で同じプログラムを実行し、4 本のメモリを比較する。

対応しているオペランド:

- `$m`/`$n`/`$r`/`$s` の直接メモリ参照。
- `wl = 1`（`$m0v` など）と `wl = 2`（`$lm0v` など）。
- FMA、MUL、ADD、PASSA。
- T 間接、base レジスタ、`j`、`neg`/`ext`/`rnd`、マスク、forwarding はまだ不可。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_mau -- 1000
```

結果:

- 1,000 行で mismatch 0。
- CPU 2.79 秒、GPU 17.4 ms。

### mauf forwarding

MAU 行の後で各 PE の `mauf` を更新し、`$mauf` をソースに取れるようにした。
`gpu_vsm_mau` の生成プログラムには `fvadd $rNv $mauf $nNv` も含まれる。

- 1,000 行（forward を含む）で mismatch 0。
- CPU 1.28 秒、GPU 26.6 ms。

`aluf`、`lbf`、`mreadf` はまだ未対応。

### アクセス長と neg

オペランドごとに `wl = 1/2/4` を持てるようにした。
同じ行でも `$llm0v`（4 ワード）と `$lr0v`（2 ワード）を混在できる。
f32 のレーンは 2 本で、ソースの `wl` が 1 なら 2 本目は 0 として読む。
`wl = 4` のデスティネーションは 3、4 ワード目に 0 を書く。
`-$r0v` のような neg も、f32 の符号ビット反転として扱う。

`gpu_coverage` で実プログラムの MAU 行のうち何割を今のカーネルが扱えるか数えられる。

```sh
cd viz/core
cargo run --release --bin gpu_coverage -- benchmarks/mnist_train_step.vsm
```

現状:

- MAU 式 724 個のうち 292 個が対応。
- PE 行 2,635 のうち、対応 MAU だけで構成される行は 292。
- 残りは `aluf`/`lbf`/`mreadf` の forward が 255、wl=4 が 203、neg が 160（重複あり）。

## ALU Passa と aluf

`fpassa` を ALU カーネルで実行し、`aluf` を VRAM に保持する。
MAU 行は `$aluf` をソースに取れる。

`gpu_vsm_alu` は `fpassa` と `$aluf` を使う MAU 行を交互に並べて比較する。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_alu -- 1000
```

- 1,000 行で mismatch 0。
- CPU 0.60 秒、GPU 15.5 ms。

`gpu_coverage` の現状:

- MAU 式 724 個のうち 435 個が対応（`aluf` の分が増えた）。
- ALU 式 924 個のうち `fpassa` の 256 個が対応。
- すべての式が対応する行は 256。

次は `ixor` と OMR（マスクレジスタ）への書き込み、およびマスク付き MAU 書き込み。

## ALU Xor と OMR

`ixor` を ALU カーネルに追加し、デスティネーションとして OMR（マスクレジスタ）を扱えるようにした。
OMR は PE ごとに 16 エントリを VRAM に持ち、`ixor` のフラグ nibble をサイクルごとに書く。

`gpu_vsm_alu` は `fpassa`、`ixor ... $omr1`、`$aluf` を使う MAU 行を混ぜて実行し、4 本のメモリと OMR を比較する。

- 1,000 行で mismatch 0。
- CPU 0.64 秒、GPU 21.4 ms。
- ALU 式 924 個のうち 512 個（`fpassa` と `ixor`）が対応。
- すべての式が対応する行は 512。

次は OMR を使ったマスク付きの MAU 書き込み。

## マスク付き MAU

`mask` ディレクティブとオペランドマスクを解決し、MAU の書き込みに適用する。
マスクの種類は「なし」「OMR エントリ」「固定パターン」で、`ll` のときは 1 ワード 1 ビット、
そうでないときは下位 16 bit 単位でマージする。

`gpu_vsm_mask` は `ixor $omr1`、`maskn 1`、マスク付き `fvadd`、`mask 0` を並べて実行し、
4 本のメモリと OMR を比較する。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_mask -- 500
```

- 500 ラウンド（2,500 行）で mismatch 0。
- CPU 2.04 秒、GPU 38 ms。

## ALU Max と Rsqrt

`fmax` と `frsqrt` を ALU カーネルに追加した。
`fmax` は f32 の符号付き絶対値キーで比較し、`frsqrt` は CPU と同じ `MANT5` テーブルを使う。
どちらもデスティネーションなし（`$nowrite`）を受け付け、`aluf` を更新する。

`gpu_vsm_alu` に両方を混ぜて 2,000 行を実行し、mismatch 0。
CPU 1.35 秒、GPU 41 ms。

ALU 式 924 個のうち 672 個（`fpassa`、`ixor`、`fmax`、`frsqrt`）が対応。
すべての式が対応する行は 657。

## gbfn と block-float

`gbfn` は MAB 内の 4 PE × 2 レーンの 8 値を 1 ブロックとして block-float に変換し、`aluf` を更新する。
カーネルは 1 スレッドで 1 MAB・1 サイクルを担当し、CPU と同じ `block_float` の丸めを使う。

`gpu_vsm_alu` に `gbfn $lmNv $nowrite` を混ぜて 3,000 行を実行し、mismatch 0。
CPU 3.04 秒、GPU 56.5 ms。

ALU 式 924 個のうち 752 個（`fpassa`、`ixor`、`fmax`、`frsqrt`、`gbfn`）が対応。
すべての式が対応する行は 729。

## msr、zero、imm

- `msr` は MAB 内の次の PE のバスを読み、`[v0, v1, 0, 0]` を出力して `aluf` を更新する。
- `zero` は全ワード 0 のバスを作る。
- `imm` は即値バスを作る。`u` のときは `[v, 0, v, 0]`、そうでなければ 4 ワードすべて `v`。
- デスティネーションはメモリまたは `$nowrite`。T レジスタへの書き込みはまだ未対応。

`gpu_vsm_alu` に 3 つを混ぜて 3,000 行を実行し、mismatch 0。
CPU 5.30 秒、GPU 59.2 ms。

ALU 式 985 個（zero/imm を含む）のうち 892 個が対応。
すべての式が対応する行は 868。

## T レジスタ

PE ごとに T の 16 ワードを VRAM に持つ。
ALU は T をソースとして読め、`imm`/`zero`/`fpassa` などは T に書ける。
`gpu_vsm_alu` は `imm ... $t`、`fpassa $t $rNv`、`zero $t` を混ぜ、
T の全ワードも比較する。

3,000 行で mismatch 0。CPU 6.07 秒、GPU 104 ms。

ALU 式 985 個のうち 909 個、MAU 式 724 個のうち 478 個が対応。
すべての式が対応する行は 885。

## L1BM の読み出し

L1BM を 64 L1B × 8,192 ロングワード（4 MB）で VRAM に持つ。
`l1bmd` の Distrib と `l1bmm` の Mbcast をカーネル化し、PE のメモリへ書く。

`gpu_vsm_l1` はランダムな L1BM をアップロードし、`l1bmd` と `l1bmm` を交互に実行して
PE メモリを比較する。

- 500 行で mismatch 0。
- CPU 1.41 秒、GPU 7.9 ms。

L1 式 292 個のうち 148 個（読み出しのみ）が対応。
すべての式が対応する行は 1,033。

L1BM への書き込み（`l1bmm@`）、L2BM、行列、MV はまだ未対応。

## L1BM への書き込み

`l1bmm@mab` の Mwrite をカーネル化し、指定 MAB の 4 PE がサイクルごとに 2 ロングワードを
L1BM へ書く。`l1bmp` の Pbcast 読み出しも追加した。

`gpu_vsm_l1` は書き込みと読み出しを混ぜ、L1BM と PE メモリの両方を比較する。

- 500 行で mismatch 0。
- CPU 1.06 秒、GPU 5.5 ms。
- L1 式 292 個のうち 264 個が対応。
- すべての式が対応する行は 1,149。

L2BM、行列、MV、および L1BM の turnaround レジスタはまだ未対応。

## L2BM の転送

L2BM を 8 L2B × 32,768 ロングワード（8 MB）で VRAM に持つ。
次の 3 種類をカーネル化した。

- `l2bmd` の Distrib（L2BM → L1BM）
- `l2bmb` の Bcast（L2BM → L1BM）
- `l2bm@l1b` の FromL1b（L1BM → L2BM）

`gpu_vsm_l2` は 3 種類を混ぜ、L1BM と L2BM の両方を比較する。

- 500 行で mismatch 0。
- CPU 11.7 ms、GPU 3.0 ms（データ移動が中心なので差は小さい）。
- L2 式 493 個のうち 377 個が対応。
- すべての式が対応する行は 1,526（PE 行 2,635 中、約 58%）。

L2BM の reduction、内部マルチキャスト、行列はまだ未対応。

## L2BM の縮約と内部マルチキャスト

RRN の縮約をカーネル化し、`l2bmr<rrn>`（Reduce）、`l2bmr2<rrn>`（Reduce2）、
`l2bmi@<l1bset>`（Imcast）を実行できるようにした。

- `l2bmr` は L1B 集合で選んだ 8 L1B（集合の外は単位元）の 16 長語をサイクルごとに縮約し、L2BM へ書く。
- `l2bmr2` は隣り合う 2 L1B を 1 組として 4 組を縮約する。
- `l2bmi` は `immode` が同じ L1B グループ内で、集合に含まれる L1B から 16 長語をコピーする
  （自分自身へのコピーは CPU と同じく書かない）。

対応する RRN は 24 種類すべて:
`dfadd`/`ffadd`/`hfadd`、`dmax`/`fmax`/`hmax`、`dmin`/`fmin`/`hmin`、
`liadd`/`iiadd`/`siadd`、`lband`/`iband`/`sband`、`land`/`iand`/`sand`、
`lbor`/`ibor`/`sbor`、`lor`/`ior`/`sor`。

浮動小数点加算は CPU の `rrn::fadd` と同じく、最大指数に仮数を RNE で丸めながら桁合わせし、
符号付きで厳密に加算してから一度だけ丸める。
`gpu_vsm_l2red` は `mnist_train_step.vsm` に出てくる `l2bmrffadd` と同じ形の行に、
L1B 部分集合、`l2bmr2`、`l2bmi`、全 RRN を混ぜて実行し、L1BM と L2BM の全ワードを比較する。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_l2red -- 512
```

結果:

- 512 行（l2bmr 258、l2bmr2 76、l2bmi 178）で mismatch 0。
  l2bmr と l2bmr2 はそれぞれ 24/24 の RRN を実行し、l2bmr は全 RRN を全 L1B 集合と部分集合の両方で実行。
- CPU 70 ms、GPU 4.7 ms。
- 4,096 行でも mismatch 0（CPU 512 ms、GPU 36 ms）。
- 指数を狭い範囲にそろえた half/single/double の追加ストレス（各 2,048 行）でも mismatch 0。

`gpu_coverage` の現状:

- L2 式 493 個のうち 387 個が対応（`mnist_train_step.vsm` の L2 縮約 10 個を含む）。
- すべての式が対応する行は 1,536（PE 行 2,635 中、約 58%）。

`l2bmb2`（Bcast2）と、L1B 集合を指定した `l2bmd` の Distrib はまだ未対応。

## MV（PDM/DRAM）

PDM と DRAM をデバイスに置き、MV を 1 文 1 カーネル（`mv_line`）で実行する。

- PDM は 4 グループ × 524,288 ロングワード（16 MB）をそのまま持つ。
- DRAM の CPU 側の全容量は 4 × 512 Mi ロングワード = 128 GiB なので、デバイスには
  グループあたり `dram_longs` ロングワードだけを持つ。`allocate_state_with_mv` で確保し、
  範囲外を触る文は `run_mv_line` が拒否する。必要な容量は `MvLine::dram_longs_needed`
  で見積もれる（実際のアクセスは `addr + size` 未満に収まる）。
- L2BM は既存の 8 × 32,768 ロングワードのバッファをそのまま使う。

対応しているデータフロー:

- `mvp`: 単一グループ間、およびグループを省略した 4 グループ並列。
- `mvb`: PDM → 全 L2BM、DRAM → 全 L2BM。
- `mvb2`: DRAM → 各グループの両 L2BM。
- `mvb4`: DRAM → 全 L2BM（グループ分配）。
- `mvd`: PDM ↔ L2BM、PDM ↔ DRAM。
- `mvr<op>`、`mvr2<op>`、`mvr4<op>`: 8/2/4 値の reduction。
  RRN は fadd（half/single/double）と iadd、band、and、bor、or、max、min。
  fadd は CPU と同じ 2 段階の丸めを行う。
- `mvnop`。
- 間接 DRAM アクセス（`$di...`）は CPU も未対応なので対象外。

`mvp` のコピー元とコピー先が同じメモリレベル・同じグループにある場合、CPU は
全読み出しの後に全書き込みを行う。GPU ではソースをスクラッチに落としてから書く
2 パス実行にし、重なった範囲でもコピーとして一致させる。スクラッチの大きさは
`allocate_state_with_mv` の第 2 引数で指定する。

`gpu_vsm_mv` は PDM/DRAM/L1BM/L2BM をランダム値で埋め、CPU の `Sim` と GPU で
同じ MV 文を実行して 4 つのメモリを比較する。合成文（`--seed` で再現可能）と、
実プログラムから MV 文だけを抽出するモードがある。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_mv -- 400
cargo run --release --bin gpu_vsm_mv -- --program benchmarks/mnist_train_step.vsm
```

`mnist_train_step.vsm` の MV 168 文をすべて実行した結果:

- 168 文すべて対応、mismatch 0（PDM/DRAM/L1BM/L2BM）。
- CPU 約 19 ms、GPU 1〜2 ms（ランダム初期状態の転送は含まない）。
- 合成 400 文も複数の seed で mismatch 0。`mvp` の重なり、PDM/L2BM の
  アドレス折り返し、half/double の fadd、整数 RRN を含む。

## 行列レジスタ（gmwrite / gmread / gmmul）

行列レジスタを 1,024 MAB × 2 面（x/y）× 16 物理行 × 8 ワードの u32（1 MiB）で VRAM に保持する。
`GpuState` はこのバッファと、行列読み出しの forwarding である `mreadf` も持つ。

追加したカーネル:

- `mat_write_line`: `fmwrite`/`gmwrite`。1 スレッドが 1 MAB・1 サイクルを担当し、4 PE の 2 語ずつから物理行 8 語を作る。F/G は同じ配置で、論理行 i は物理行 2i に対応する。
- `mat_read_line`: `fmread`/`gmread`。1 スレッド 1 PE。論理行 2p と 2p+1 の要素を 2 レーンとして PE メモリへ書き、`mreadf` も更新する。`$nowrite` は `mreadf` だけを更新する。
- `mat_mau_line`: `fmfma`/`fmmul`/`fmadd`/`fmpassa` と G 版（`gmfma`、`gmmul` など）。1 スレッド 1 MAB が 4 サイクル分の x/y を先に読み、8 行の block-float 内積 + y を 1 回だけ丸める。CPU の `float::bf_dot` と `float::mat_fma` を CUDA に移植した。`mauf` も更新する。

対応範囲:

- F/G は 32 bit 要素なので同じ物理行レイアウトを使う。F は列 0,2,4,6 の 4 項、G は 8 項（pseudo-single、下位 5 bit を捨てる）の内積になる。
- ソースは LM0/LM1/GRF0/GRF1、`$aluf`/`$mauf`、neg、`wl = 1/2/4`。デスティネーションは PE メモリと `$nowrite`。
- D/H 精度、マスク付きの行列読み出し・MAU 書き込み、`ext`/`rnd`、T をソースにする行列演算はまだ未対応。
- CPU は不正な block-float 入力を書き込み時にエラーにするが、GPU 側はエラーにせずビットを書く。テストは正しい block-float 入力だけを使う。

`gpu_vsm_matrix` は gmwrite/gmread/gmmul と f32 版、`fpassa` による `aluf` 生成、`$nowrite` 読み出しを混ぜ、
行列レジスタと 4 本の PE メモリを比較する。

```sh
cd viz/core
cargo run --release --bin gpu_vsm_matrix -- 100
```

結果:

- 1,300 行で mismatch 0。
- CPU 約 5 秒、GPU 約 55〜75 ms。
- 6,500 行でも mismatch 0（CPU 約 30 秒、GPU 約 290 ms）。
- `gpu_coverage` の matrix 式は 216 個のうち 184 個が対応（書き込み 96/112、読み出し 40/56、MAU 48/48）。
  残り 32 個は double 精度の `dmwrite`/`dmread`。

## 現状（GPU 全体実行）

`gpu_run_program` が `benchmarks/mnist_train_step.vsm` を GPU だけで実行する。

```sh
cd viz/core
cargo run --release --bin gpu_run_program -- benchmarks/mnist_train_step.vsm
```

結果:

- 2,635 PE 行、168 MV 文を実行し、mismatch 0。
- CPU 1.74 秒、GPU 36 ms。
- 比較対象は LM0/LM1/GRF0/GRF1、行列レジスタ、OMR、L1BM、L2BM、PDM、DRAM。

対応済み:

- ALU/MAU、マスク、`mauf`/`aluf`/`mreadf`、T。
- L1BM の読み書き・Gather・reduction。
- L2BM の全転送・reduction・内部マルチキャスト。
- 行列の F/G/D（write/read/matrix MAU）。
- MV の全 168 文。

制約:

- デバイスの DRAM はプログラムが必要とする 264,064 ロングワード/グループだけを持つ。
  CPU の全 128 GiB は載せない。範囲外は拒否する。
- マスク付きの行列読み出し・MAU 書き込み、L1BM turnaround `$lbi`、
  不正 block-float 入力のエラー検出は未対応。
- カーネルは NVRTC + CUDA Driver API で実行時にコンパイルする。

## 全命令への拡張

SDM 3.6 の全 PE 命令式への拡張を開始した。現状と不足は
[gpu-instruction-coverage.md](gpu-instruction-coverage.md) にまとめている。
直近では ALU の Min、Sub、Inc、Dec、Not、Lnot、And、Or を追加した。
