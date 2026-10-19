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
- ALU、MAU（half/double を含む）、マスク、forwarding、msl/msr、block-float、L1BM/L2BM、行列、MV のカーネル。
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

L2BM の reduction、内部マルチキャスト、行列、MV はまだ未対応。
