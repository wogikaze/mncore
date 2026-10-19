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
